#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tools/julia-oracle.jl
#
# Pre-proof numerical oracle. Given an A2ML descriptor of a lemma,
# computes the lemma's claimed value via impl/tropical/TropicalDeterminant.jl
# and prints a verdict line. Disagreement = the lemma STATEMENT is suspect
# (not the proof) — Burrower's Algebraist consumes this as
# `learning.kind = oracle-counter-example` and skips the Isabelle attempt.
#
# Why A2ML, not JSON: estate-wide policy "no JSON emit"
# (feedback_no_json_emit_a2ml.md). Tools emit A2ML for data, Nickel for
# schemas. JSON is reserved for socket-level interop (BI-1) where the
# protocol is constrained externally.
#
# Descriptor format (one [oracle-input] block, optional [oracle-fuzz]):
#
#   [oracle-input]
#   family   = "tropical-determinant-min"
#   matrix   = [[1, 2], [3, 4]]
#   expected = 4              # claimed value of det_min(matrix)
#
#   [oracle-fuzz]               # safe-learning (c) — adversarial test gen
#   family            = "tropical-determinant-min"
#   matrix-size       = 3
#   value-range       = [0, 9]
#   trials            = 50
#   claim-template    = "det_min(A) == minimum(A[i,π[i]] for i,π enumeration)"
#   # oracle generates random matrices, recomputes det_min from scratch
#   # via permutation enumeration, asserts agreement.
#
# Verdict lines (one per descriptor stanza):
#
#   oracle: agree (family=..., computed=..., expected=...)
#   oracle: disagree (family=..., computed=..., expected=...)
#   oracle: inapplicable (reason=...)
#   oracle: fuzz-clean (family=..., trials=..., disagreements=0)
#   oracle: fuzz-counter (family=..., trials=..., disagreements=N, sample=...)

# ------------------------------------------------------------------
# A2ML mini-parser. Hand-rolled to avoid pulling a TOML dependency
# we'd then have to vendor; the format here is a TOML-ish subset.
# ------------------------------------------------------------------

module A2MLMini

export parse_a2ml

"""
    parse_a2ml(path::AbstractString) -> Dict{String, Dict{String, Any}}

Parse a TOML-like A2ML descriptor: `[section]` headers, `key = value`
lines. Values are scalars (Int, Float64, String) or vectors (possibly
nested). Comments start with `#`.

Deliberately minimal — we accept exactly the descriptor shapes the
oracle needs today.
"""
function parse_a2ml(path::AbstractString)
    sections = Dict{String, Dict{String, Any}}()
    current = ""
    sections[current] = Dict{String, Any}()
    open(path, "r") do io
        for raw in eachline(io)
            line = strip(raw)
            isempty(line) && continue
            startswith(line, "#") && continue
            if startswith(line, "[") && endswith(line, "]")
                current = strip(line[2:end-1])
                if !haskey(sections, current)
                    sections[current] = Dict{String, Any}()
                end
            elseif occursin('=', line)
                eq = findfirst('=', line)
                key = strip(line[1:eq-1])
                val_str = strip(line[eq+1:end])
                # Trim trailing comment
                hash = findfirst('#', val_str)
                if hash !== nothing
                    # Don't strip when '#' is inside quoted string
                    quoted = startswith(val_str, '"') &&
                             findfirst('"', val_str[2:end]) !== nothing &&
                             hash > 1 + findfirst('"', val_str[2:end])
                    if !quoted
                        val_str = strip(val_str[1:hash-1])
                    end
                end
                sections[current][key] = parse_value(val_str)
            end
        end
    end
    delete!(sections, "")  # drop the implicit pre-header bin
    sections
end

function parse_value(s::AbstractString)
    s = strip(s)
    if startswith(s, '"') && endswith(s, '"')
        return s[2:end-1]
    elseif startswith(s, "[") && endswith(s, "]")
        return parse_list(s)
    else
        # Try integer first, then float, then return as string.
        n = tryparse(Int, s)
        n !== nothing && return n
        f = tryparse(Float64, s)
        f !== nothing && return f
        return s
    end
end

function parse_list(s::AbstractString)
    inner = s[2:end-1]
    isempty(strip(inner)) && return Any[]
    # Split on top-level commas only (depth-aware over [ ]).
    items = String[]
    depth = 0
    last = 1
    for (i, c) in enumerate(inner)
        if c == '['
            depth += 1
        elseif c == ']'
            depth -= 1
        elseif c == ',' && depth == 0
            push!(items, String(strip(inner[last:i-1])))
            last = i + 1
        end
    end
    push!(items, String(strip(inner[last:end])))
    map(parse_value, items)
end

end # module A2MLMini

# ------------------------------------------------------------------
# Oracle main
# ------------------------------------------------------------------

push!(LOAD_PATH, joinpath(@__DIR__, "..", "impl", "tropical"))
import .A2MLMini: parse_a2ml

# Load the determinant module from impl/tropical/.
include(joinpath(@__DIR__, "..", "impl", "tropical", "TropicalDeterminant.jl"))
using .TropicalDeterminant

using Random: Random, MersenneTwister

function emit_input_verdict(payload::AbstractDict)
    family = get(payload, "family", "")
    isempty(family) && return println("oracle: inapplicable (reason=missing family)")
    verdict, info = TropicalDeterminant.evaluate_descriptor(family, payload)
    if verdict === :agree
        println("oracle: agree (family=$family, computed=$info, expected=$(payload["expected"]))")
    elseif verdict === :disagree
        computed, expected = info
        println("oracle: disagree (family=$family, computed=$computed, expected=$expected)")
    else
        println("oracle: inapplicable (reason=$info)")
    end
end

function emit_fuzz_verdict(payload::AbstractDict)
    family = get(payload, "family", "")
    isempty(family) && return println("oracle: inapplicable (reason=missing family)")
    n        = Int(get(payload, "matrix-size", 3))
    range    = get(payload, "value-range", Any[0, 9])
    trials   = Int(get(payload, "trials", 50))
    seed_val = Int(get(payload, "seed", 0xCAFE))
    rng = MersenneTwister(seed_val)
    lo, hi = Int(range[1]), Int(range[2])

    # The fuzz contract: for every sampled matrix A, the family's
    # computed value should equal the value derived from a fresh
    # permutation enumeration.
    disagreements = 0
    sample = nothing
    for _ in 1:trials
        A = rand(rng, lo:hi, n, n)
        # Re-derive ground truth by independent permutation enumeration:
        all_sums = TropicalDeterminant.all_perm_sums(A)
        ground = if family == "tropical-determinant-min"
                     minimum(s for (_, s) in all_sums)
                 elseif family == "tropical-determinant-max"
                     maximum(s for (_, s) in all_sums)
                 else
                     return println("oracle: inapplicable (reason=fuzz unknown family: $family)")
                 end
        verdict, info = TropicalDeterminant.evaluate_descriptor(
            family, Dict("matrix" => A, "expected" => ground)
        )
        if verdict !== :agree
            disagreements += 1
            sample === nothing && (sample = A)
        end
    end

    if disagreements == 0
        println("oracle: fuzz-clean (family=$family, trials=$trials, disagreements=0)")
    else
        println("oracle: fuzz-counter (family=$family, trials=$trials, disagreements=$disagreements, sample=$sample)")
    end
end

function main(args)
    if length(args) != 1
        println(stderr, "usage: julia tools/julia-oracle.jl <descriptor.a2ml>")
        exit(2)
    end
    path = args[1]
    isfile(path) || (println(stderr, "oracle: descriptor not found: $path"); exit(2))

    sections = parse_a2ml(path)
    if haskey(sections, "oracle-input")
        emit_input_verdict(sections["oracle-input"])
    end
    if haskey(sections, "oracle-fuzz")
        emit_fuzz_verdict(sections["oracle-fuzz"])
    end
    if !haskey(sections, "oracle-input") && !haskey(sections, "oracle-fuzz")
        println("oracle: inapplicable (reason=descriptor has no [oracle-input] or [oracle-fuzz])")
    end
end

isinteractive() || main(ARGS)
