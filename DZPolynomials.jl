module DZPolynomials

export Monomial, Polynomial, uses_variable, uses_all_variables,
    apply_transposition, apply_cycle, apply_negation, apply_signflip,
    apply_transposition!, apply_cycle!, apply_negation!, apply_signflip!

################################################################################

const Monomial{T, N, I} = Pair{NTuple{N, I}, T}

const Polynomial{T, N, I} = Vector{Monomial{T, N, I}}

function uses_variable(p::Polynomial{T, N, I}, i::Int) where {T, N, I}
    @inbounds for (m, c) in p
        if !iszero(m[i])
            return true
        end
    end
    return false
end

function uses_all_variables(p::Polynomial{T, N, I}) where {T, N, I}
    for i = 1 : N
        if !uses_variable(p, i)
            return false
        end
    end
    return true
end

################################################################################

apply_transposition(m::Monomial{T, 0, I}) where {T, I} = m
apply_transposition(m::Monomial{T, 1, I}) where {T, I} = m
apply_cycle(m::Monomial{T, 0, I}) where {T, I} = m
apply_signflip(m::Monomial{T, 0, I}) where {T, I} = m

function apply_transposition(m::Monomial{T, N, I}) where {T, N, I}
    ((i, j, k...), c) = m
    return (j, i, k...) => c
end

function apply_cycle(m::Monomial{T, N, I}) where {T, N, I}
    ((i, j...), c) = m
    return (j..., i) => c
end

function apply_negation((m, c)::Monomial{T, N, I}) where {T, N, I}
    return m => -c
end

function apply_signflip(m::Monomial{T, N, I}) where {T, N, I}
    ((i, j...), c) = m
    return (i, j...) => ifelse(iszero(i & one(I)), c, -c)
end

################################################################################

function apply_transposition!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_transposition(p[i])
    end
    return p
end

function apply_cycle!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_cycle(p[i])
    end
    return p
end

function apply_negation!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_negation(p[i])
    end
    return p
end

function apply_signflip!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_signflip(p[i])
    end
    return p
end

################################################################################

end # module DZPolynomials
