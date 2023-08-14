#!/usr/bin/env julia
push!(LOAD_PATH, @__DIR__)
using DiophantinePolynomials


function structure_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}}
) where {N}
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        if is_positive_definite(p)
            lines[i] = "$(p) : positive-definite"
            push!(to_delete, j)
        elseif is_negative_definite(p)
            lines[i] = "$(p) : negative-definite"
            push!(to_delete, j)
        end
    end
    deleteat!(unsolved, to_delete)
    return nothing
end


function next_partition!(x::Vector{T}) where {T}
    _one = one(T)
    @inbounds begin
        n = length(x)
        if n <= 1
            return false
        end
        xn = x[n]
        xn1 = x[n-1]
        if !iszero(xn1)
            x[n-1] = xn1 - _one
            x[n] = xn + _one
            return true
        end
        i = n - 2
        while !iszero(i)
            xi = x[i]
            if !iszero(xi)
                x[i] = xi - _one
                if iszero(xn)
                    x[i+1] += _one
                else
                    x[i+1] += xn + _one
                    x[n] = zero(T)
                end
                return true
            end
            i -= 1
        end
        return false
    end
end


struct L1BallIterator{T}
    dense_point::Vector{T}
    sparse_point::Vector{Pair{Int,T}}
    sign_pattern::Array{UInt,0}
    function L1BallIterator(n::T, len::Int) where {T}
        dense_point = zeros(T, len)
        if (n > 0) && (len > 0)
            @inbounds dense_point[1] = n
            sparse_point = [1 => n]
        else
            sparse_point = Pair{Int,Int}[]
        end
        sign_pattern = fill(UInt(0))
        return new{T}(dense_point, sparse_point, sign_pattern)
    end
end


function step!(it::L1BallIterator{T}) where {T}
    dense = it.dense_point
    sparse = it.sparse_point
    s = it.sign_pattern[] + 1
    if s < (UInt(1) << length(sparse))
        it.sign_pattern[] = s
        return true
    else
        it.sign_pattern[] = UInt(0)
        if !next_partition!(dense)
            return false
        end
        empty!(sparse)
        for (i, c) in enumerate(dense)
            if !iszero(c)
                push!(sparse, i => c)
            end
        end
        @assert length(sparse) < 8 * sizeof(UInt)
        return true
    end
end


function get_point(::Val{N}, it::L1BallIterator{T}) where {N,T}
    result = ntuple(_ -> zero(T), Val{N}())
    s = it.sign_pattern[]
    for (i, c) in it.sparse_point
        result = Base.setindex(result, ifelse(isodd(s), -c, +c), i)
        s >>= 1
    end
    return result
end


function l1_ball(::Val{N}, radius::T) where {N,T}
    result = NTuple{N,T}[]
    it = L1BallIterator(radius, N)
    while true
        push!(result, get_point(Val{N}(), it))
        if !step!(it)
            break
        end
    end
    return result
end


function root_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}},
    k::Int
) where {N}
    ball = l1_ball(Val{N}(), k)
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        root = find_root(p, ball)
        if !isnothing(root)
            lines[i] = "$(p) : $(root)"
            push!(to_delete, j)
        end
    end
    deleteat!(unsolved, to_delete)
    return length(ball)
end


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


function has_root_modulo(
    p::DiophantinePolynomial{N}, k::T, ::Type{U}
) where {N,T,U}
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


function modulus_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}},
    k::Int
) where {N}
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        if !has_root_modulo(p, k, UInt64)
            lines[i] = "$(p) : modulus $(k)"
            push!(to_delete, j)
        end
    end
    deleteat!(unsolved, to_delete)
    return nothing
end


function write_atomic(lines::Vector{String}, path::String)
    temp_path, io = mktemp()
    for line in lines
        println(io, line)
    end
    mv(temp_path, path; force=true)
end


function main(::Val{N}, path::String) where {N}

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

        old_length = length(unsolved)
        structure_search!(lines, unsolved)
        new_length = length(unsolved)

        println("Solved $(old_length - new_length) equations by structural analysis.")
        println("$(new_length) unsolved equations remain.")
        flush(stdout)

        if old_length != new_length
            write_atomic(lines, path)
        end

        if isempty(unsolved)
            return nothing
        end

    end

    next_modulus = 2
    for k = zero(Int):typemax(Int)

        old_length = length(unsolved)
        ball_size = root_search!(lines, unsolved, k)
        new_length = length(unsolved)

        println("Solved $(old_length - new_length) equations at radius $(k).")
        println("$(new_length) unsolved equations remain.")
        flush(stdout)

        if old_length != new_length
            write_atomic(lines, path)
        end

        if isempty(unsolved)
            return nothing
        end

        while next_modulus^N <= ball_size

            old_length = length(unsolved)
            modulus_search!(lines, unsolved, next_modulus)
            new_length = length(unsolved)

            println("Solved $(old_length - new_length) equations at modulus $(next_modulus).")
            println("$(new_length) unsolved equations remain.")
            flush(stdout)

            if old_length != new_length
                write_atomic(lines, path)
            end

            if isempty(unsolved)
                return nothing
            end

            next_modulus += 1

        end

    end

    return nothing
end


main(Val(parse(Int, ARGS[1])), ARGS[2])
