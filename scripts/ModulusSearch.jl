#!/usr/bin/env julia
push!(LOAD_PATH, @__DIR__)
using DiophantinePolynomials


struct ModularInteger{T,U} <: Number
    value::T
    modulus::T
end


@inline function Base.:+(
    x::ModularInteger{T,U}, y::ModularInteger{T,U}
) where {T,U}
    k = x.modulus
    @assert k == y.modulus
    @assert zero(T) <= x.value < k
    @assert zero(T) <= y.value < k
    result = x.value + y.value
    return ModularInteger{T,U}(ifelse(result >= k, result - k, result), k)
end


@inline function Base.:*(
    x::ModularInteger{T,U}, y::ModularInteger{T,U}
) where {T,U}
    k = x.modulus
    @assert k == y.modulus
    @assert zero(T) <= x.value < k
    @assert zero(T) <= y.value < k
    result = (U(x.value) * U(y.value)) % U(k)
    return ModularInteger{T,U}(result % T, k)
end


function has_root_modulo(p::DiophantinePolynomial{N}, k::T, ::Type{U}) where {N,T,U}
    range = zero(T):k-one(T)
    for x in Iterators.product(ntuple(_ -> range, Val{N}())...)
        result = ModularInteger{T,U}(zero(T), k)
        for (c, m) in p.terms
            c_m = ModularInteger{T,U}(mod(c, k) % T, k)
            x_m = ModularInteger{T,U}.(powermod.(x, m, k), k)
            result += *(c_m, x_m...)
        end
        if iszero(result.value)
            return true
        end
    end
    return false
end


function main(::Val{N}, path::String, radius::UInt32) where {N}

    println("Reading file ", path, "...")
    flush(stdout)

    unsolved = Pair{Int,DiophantinePolynomial{N}}[]
    lines = readlines(path)
    for (i, line) in enumerate(lines)
        if !(':' in line)
            push!(unsolved, i => DiophantinePolynomial{N}(line))
        end
    end

    println("Read ", length(lines), " lines.")
    println("Loaded ", length(unsolved), " unsolved equations.")
    flush(stdout)

    if isempty(unsolved)
        return nothing
    end

    let
        to_delete = Int[]
        for (j, (i, p)) in enumerate(unsolved)
            if is_positive_definite(p)
                lines[i] = "$(to_string(p)) : positive-definite"
                push!(to_delete, j)
            elseif is_negative_definite(p)
                lines[i] = "$(to_string(p)) : negative-definite"
                push!(to_delete, j)
            end
        end
        deleteat!(unsolved, to_delete)
    end

    for k = UInt32(2):radius
        to_delete = Int[]
        for (j, (i, p)) in enumerate(unsolved)
            if !has_root_modulo(p, k, UInt64)
                lines[i] = "$(to_string(p)) : modulus $(k)"
                push!(to_delete, j)
            end
        end
        deleteat!(unsolved, to_delete)
        if isempty(unsolved)
            break
        end
    end

    println(length(unsolved), " unsolved equations remain.")

    temp_path, io = mktemp()
    for line in lines
        println(io, line)
    end

    mv(temp_path, path; force=true)
    return nothing

end


main(Val(parse(Int, ARGS[1])), ARGS[3], parse(UInt32, ARGS[2]))
