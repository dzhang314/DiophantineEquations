#!/usr/bin/env julia
push!(LOAD_PATH, @__DIR__)
using DiophantinePolynomials


function incr_partition!(x::Vector{T}) where {T}
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


struct SignedPartitionIterator{T}
    dense_partition::Vector{T}
    sparse_partition::Vector{Pair{Int,T}}
    sign_pattern::Array{UInt,0}
    function SignedPartitionIterator(n::T, len::Int) where {T}
        dense_partition = zeros(T, len)
        if n > 0 && len > 0
            @inbounds dense_partition[1] = n
            sparse_partition = [1 => n]
        else
            sparse_partition = Pair{Int,Int}[]
        end
        sign_pattern = fill(UInt(0))
        return new{T}(dense_partition, sparse_partition, sign_pattern)
    end
end


function step!(it::SignedPartitionIterator{T}) where {T}
    dense = it.dense_partition
    sparse = it.sparse_partition
    s = it.sign_pattern[] + 1
    if s < (UInt(1) << length(sparse))
        it.sign_pattern[] = s
        return true
    else
        it.sign_pattern[] = UInt(0)
        if !incr_partition!(dense)
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


function get_partition(::Val{N}, it::SignedPartitionIterator{T}) where {N,T}
    result = ntuple(_ -> zero(T), Val{N}())
    s = it.sign_pattern[]
    @inbounds for (i, c) in it.sparse_partition
        result = Base.setindex(result, ifelse(iseven(s), c, -c), i)
        s >>= 1
    end
    return result
end


function l1_ball(::Val{N}, radius::T) where {N,T}
    result = NTuple{N,T}[]
    it = SignedPartitionIterator(radius, N)
    while true
        push!(result, get_partition(Val{N}(), it))
        if !step!(it)
            break
        end
    end
    return result
end


function main(::Val{N}, path::String, radius::T) where {N,T}

    unsolved = Pair{Int,Polynomial{N}}[]
    lines = readlines(path)
    for (i, line) in enumerate(lines)
        if !(':' in line)
            push!(unsolved, i => parse_polynomial(Val{N}(), line))
        end
    end

    println("Reading file ", path, "...")
    println("Read ", length(lines), " lines.")
    println("Loaded ", length(unsolved), " unsolved equations.")

    for k = zero(T):radius
        ball = l1_ball(Val{N}(), k)
        to_delete = Int[]
        for (j, (i, p)) in enumerate(unsolved)
            root = find_root(p, ball)
            if !isnothing(root)
                lines[i] = "$(to_string(p)) : $(root)"
                push!(to_delete, j)
            end
        end
        deleteat!(unsolved, to_delete)
    end

    println(length(unsolved), " unsolved equations remain.")

    temp_path, io = mktemp()
    for line in lines
        println(io, line)
    end

    mv(temp_path, path; force=true)
    return nothing

end


main(Val(parse(Int, ARGS[1])), ARGS[3], parse(Int, ARGS[2]))
