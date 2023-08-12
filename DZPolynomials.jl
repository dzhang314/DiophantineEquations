module DZPolynomials

export Monomial, Polynomial, coefficient_of,
    find_root, has_root_modulo, uses_variable, uses_all_variables,
    has_linear_variable, has_divisible_variable, has_coprime_coefficients,
    is_positive_semidefinite, is_negative_semidefinite,
    is_elliptic_curve, is_weierstrass_elliptic_curve, weierstrass_coefficients,
    to_string, to_latex,
    apply_transposition, apply_cycle, apply_negation, apply_signflip,
    apply_transposition!, apply_cycle!, apply_negation!, apply_signflip!,
    incr_partition!, integer_partitions,
    HomogeneousPolynomialIterator, get_polynomial, incr_polynomial!,
    l1_ball

################################################################################

const Monomial{T,N,I} = Pair{NTuple{N,I},T}

const Polynomial{T,N,I} = Vector{Monomial{T,N,I}}

function coefficient_of(p::Polynomial{T,N,I}, m::NTuple{N,I}) where {T,N,I}
    for (n, c) in p
        if m == n
            return c
        end
    end
    return zero(T)
end

################################################################################

function is_elliptic_curve_1(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    _three = _two + _one
    found_cubic = false
    found_quadratic = false
    for ((i, j), c) in p
        if (i, j) == (_three, _zero)
            if !iszero(c)
                found_cubic = true
            end
        elseif (i, j) == (_zero, _two)
            if !iszero(c)
                found_quadratic = true
            end
        elseif i + j > _two
            return false
        end
    end
    return found_cubic && found_quadratic
end

function is_elliptic_curve_2(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    _three = _two + _one
    found_cubic = false
    found_quadratic = false
    for ((i, j), c) in p
        if (i, j) == (_zero, _three)
            if !iszero(c)
                found_cubic = true
            end
        elseif (i, j) == (_two, _zero)
            if !iszero(c)
                found_quadratic = true
            end
        elseif i + j > _two
            return false
        end
    end
    return found_cubic && found_quadratic
end

is_elliptic_curve(p::Polynomial{T,2,I}) where {T,I} =
    is_elliptic_curve_1(p) || is_elliptic_curve_2(p)
is_elliptic_curve(p::Polynomial{T,N,I}) where {T,N,I} = false

function is_weierstrass_elliptic_curve(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    _three = _two + _one
    found_cubic = false
    found_quadratic = false
    for ((i, j), c) in p
        if (i, j) == (_three, _zero)
            if !isone(c)
                return false
            end
            found_cubic = true
        elseif (i, j) == (_zero, _two)
            if !isone(c) && !isone(-c)
                return false
            end
            found_quadratic = true
        elseif i + j > _two
            return false
        end
    end
    return found_cubic && found_quadratic
end

is_weierstrass_elliptic_curve(p::Polynomial{T,N,I}) where {T,N,I} = false

function weierstrass_coefficients(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    c = coefficient_of(p, (_zero, _two))
    if isone(c)
        return (
            -coefficient_of(p, (_one, _one)),
            -coefficient_of(p, (_two, _zero)),
            coefficient_of(p, (_zero, _one)),
            coefficient_of(p, (_one, _zero)),
            -coefficient_of(p, (_zero, _zero))
        )
    elseif isone(-c)
        return (
            -coefficient_of(p, (_one, _one)),
            coefficient_of(p, (_two, _zero)),
            -coefficient_of(p, (_zero, _one)),
            coefficient_of(p, (_one, _zero)),
            coefficient_of(p, (_zero, _zero))
        )
    else
        error()
    end
end

end # module DZPolynomials
