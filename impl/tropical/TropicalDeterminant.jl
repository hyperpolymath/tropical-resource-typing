# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# TropicalDeterminant.jl
#
# Reference numerical implementation of the tropical (min-plus) determinant.
# Used by tools/julia-oracle.jl as a ground-truth oracle for the Isabelle
# proofs in Tropical_Determinants.thy: when a lemma claims a specific
# value for det_min(A), the oracle computes the value here and flags
# disagreement BEFORE Isabelle attempts the proof.
#
# Min-plus tropical determinant of an n×n matrix A:
#
#     det_min(A) = min over permutations π of sum_{i=1..n} A[i, π(i)]
#
# This is exactly the assignment / minimum-cost-perfect-matching value.
# For n ≤ ~10 the naïve permutation enumeration is fine; the oracle
# does not aspire to scale beyond hand-checked examples.

module TropicalDeterminant

using Combinatorics: permutations

export det_min, det_max, all_perm_sums, evaluate_descriptor

"""
    det_min(A::AbstractMatrix{<:Real}) -> Real

Min-plus tropical determinant. Returns the minimum over all permutations
π of the i-th row index of `sum(A[i, π[i]] for i in 1:n)`.

Throws `ArgumentError` for non-square input.
"""
function det_min(A::AbstractMatrix{<:Real})
    n, m = size(A)
    n == m || throw(ArgumentError("det_min: matrix must be square (got $(n)×$(m))"))
    n == 0 && return zero(eltype(A))
    minimum(sum(A[i, π[i]] for i in 1:n) for π in permutations(1:n))
end

"""
    det_max(A::AbstractMatrix{<:Real}) -> Real

Max-plus tropical determinant. Sibling of `det_min`; useful for
cross-checking lemmas about the dual semiring.
"""
function det_max(A::AbstractMatrix{<:Real})
    n, m = size(A)
    n == m || throw(ArgumentError("det_max: matrix must be square (got $(n)×$(m))"))
    n == 0 && return zero(eltype(A))
    maximum(sum(A[i, π[i]] for i in 1:n) for π in permutations(1:n))
end

"""
    all_perm_sums(A::AbstractMatrix{<:Real}) -> Vector{Tuple{Vector{Int}, Real}}

Return every (permutation, sum) pair. Used by the adversarial fuzzer
to surface near-ties (where the determinant is fragile under noise).
"""
function all_perm_sums(A::AbstractMatrix{<:Real})
    n, m = size(A)
    n == m || throw(ArgumentError("all_perm_sums: matrix must be square"))
    [(collect(π), sum(A[i, π[i]] for i in 1:n)) for π in permutations(1:n)]
end

"""
    evaluate_descriptor(family::String, payload::Dict) -> Tuple{Symbol, Any}

Family-dispatch entry point used by the oracle. Returns
(:agree, value), (:disagree, (computed, expected)), or
(:inapplicable, reason).

Currently supported families:
  - "tropical-determinant-min"  → expects payload["matrix"] + payload["expected"]
  - "tropical-determinant-max"  → same shape, max-plus

Add new families here as the proof inventory grows.
"""
function evaluate_descriptor(family::AbstractString, payload::AbstractDict)
    if family == "tropical-determinant-min"
        haskey(payload, "matrix")   || return (:inapplicable, "missing key: matrix")
        haskey(payload, "expected") || return (:inapplicable, "missing key: expected")
        m = _to_matrix(payload["matrix"])
        m === nothing && return (:inapplicable, "matrix not coercible to Matrix{<:Real}")
        computed = det_min(m)
        expected = payload["expected"]
        return computed == expected ? (:agree, computed) : (:disagree, (computed, expected))
    elseif family == "tropical-determinant-max"
        haskey(payload, "matrix")   || return (:inapplicable, "missing key: matrix")
        haskey(payload, "expected") || return (:inapplicable, "missing key: expected")
        m = _to_matrix(payload["matrix"])
        m === nothing && return (:inapplicable, "matrix not coercible to Matrix{<:Real}")
        computed = det_max(m)
        expected = payload["expected"]
        return computed == expected ? (:agree, computed) : (:disagree, (computed, expected))
    else
        return (:inapplicable, "unknown family: $family")
    end
end

# Coerce a vector-of-vectors (a2ml parsed) OR an already-built
# AbstractMatrix into a Matrix. Returns `nothing` on shape failure
# rather than throwing. Accepting both shapes keeps the fuzz loop
# (which already has a Matrix in hand) from having to round-trip
# through Vector{Vector}.
function _to_matrix(rows)
    if rows isa AbstractMatrix
        return rows
    end
    isempty(rows) && return zeros(Float64, 0, 0)
    rows isa AbstractVector || return nothing
    n = length(rows)
    m = length(first(rows))
    all(r isa AbstractVector && length(r) == m for r in rows) || return nothing
    M = Matrix{Float64}(undef, n, m)
    for i in 1:n, j in 1:m
        M[i, j] = Float64(rows[i][j])
    end
    M
end

end # module
