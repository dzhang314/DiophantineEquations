#!/usr/bin/env julia

push!(LOAD_PATH, @__DIR__)
using DiophantinePolynomials
using SymbolicAnalysis


################################################################################


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


################################################################################


function real_root_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}}
) where {N}
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        if !has_real_root(p)
            lines[i] = "$(p) : no real roots"
            push!(to_delete, j)
        end
    end
    deleteat!(unsolved, to_delete)
    return nothing
end


################################################################################


function write_atomic(lines::Vector{String}, path::String)
    temp_path, io = mktemp()
    for line in lines
        println(io, line)
    end
    mv(temp_path, path; force=true)
end


function structural_step!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}},
    path::String
) where {N}
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
        exit()
    end

    return nothing
end


function real_root_step!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}},
    path::String
) where {N}
    old_length = length(unsolved)
    real_root_search!(lines, unsolved)
    new_length = length(unsolved)

    println("Solved $(old_length - new_length) equations by real roots.")
    println("$(new_length) unsolved equations remain.")
    flush(stdout)

    if old_length != new_length
        write_atomic(lines, path)
    end

    if isempty(unsolved)
        exit()
    end

    return nothing
end


################################################################################


function main(
    ::Val{N}, path::String
) where {N}

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

    structural_step!(lines, unsolved, path)
    real_root_step!(lines, unsolved, path)

    return nothing
end


main(Val(parse(Int, ARGS[1])), ARGS[2])
