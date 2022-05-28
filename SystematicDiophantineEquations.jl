module SystematicDiophantineEquations

function has_coprime_coefficients(p::Polynomial{N}) where {N}
    result = 0
    for (c, m) in p
        result = gcd(result, c)
        if result == 1
            return true
        end
    end
    return false
end

################################################################################

function has_linear_variable(p::Polynomial{N}, i::Int) where {N}
    @inbounds (_, n) = p[i]
    @inbounds for (j, (_, m)) in enumerate(p)
        if i != j && !all(iszero.(min.(m, n)))
            return false
        end
    end
    return true
end

function has_linear_variable(p::Polynomial{N}) where {N}
    @inbounds for (i, (_, m)) in enumerate(p)
        if any(m .== 1) && has_linear_variable(p, i)
            return true
        end
    end
    return false
end

function is_elliptic_curve_1(p::Polynomial{2})
    found_cubic = false
    found_quadratic = false
    for (c, m) in p
        if m == (3, 0)
            if abs(c) != 1
                return false
            end
            found_cubic = true
        elseif m == (0, 2)
            if abs(c) != 1
                return false
            end
            found_quadratic = true
        else
            if sum(m) > 2
                return false
            end
        end
    end
    return found_cubic && found_quadratic
end

function is_elliptic_curve_2(p::Polynomial{2})
    found_cubic = false
    found_quadratic = false
    for (c, m) in p
        if m == (0, 3)
            if abs(c) != 1
                return false
            end
            found_cubic = true
        elseif m == (2, 0)
            if abs(c) != 1
                return false
            end
            found_quadratic = true
        else
            if sum(m) > 2
                return false
            end
        end
    end
    return found_cubic && found_quadratic
end

function is_elliptic_curve(p::Polynomial{2})
    return is_elliptic_curve_1(p) || is_elliptic_curve_2(p)
end

is_elliptic_curve(p::Polynomial{N}) where {N} = false

################################################################################

function nontrivial_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    for partition in power_of_two_partitions(height)
        iterators = [
            HomogeneousPolynomialIterator{N}(weight, degree)
            for (weight, degree) in partition
        ]
        if all(length(it.monomials) > 0 for it in iterators)
            while true
                p = get_polynomial(iterators)
                if (uses_all_variables(p) &&
                    !has_linear_variable(p) &&
                    !is_positive_semidefinite(p) &&
                    !is_negative_semidefinite(p) &&
                    !is_elliptic_curve(p) &&
                    has_coprime_coefficients(p) &&
                    has_root_modulo(p, 2) &&
                    has_root_modulo(p, 3) &&
                    has_root_modulo(p, 4) &&
                    has_root_modulo(p, 5) &&
                    !has_small_root(p))
                    push!(result, p)
                end
                if !incr_polynomial!(iterators)
                    break
                end
            end
        end
    end
    return result
end

################################################################################

end # module SystematicDiophantineEquations
