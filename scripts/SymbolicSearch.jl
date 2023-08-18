#!/usr/bin/env julia

using MathLink: WExpr, WInteger, weval, @W_str

push!(LOAD_PATH, @__DIR__)
using DiophantinePolynomials
using SymbolicAnalysis
using SymbolicAnalysis: delete, parse_bool, wolfram_variables, wolfram_polynomial


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


function real_roots_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}}
) where {N}
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        if !has_real_roots(p)
            lines[i] = "$(p) : no real roots"
            push!(to_delete, j)
        end
    end
    deleteat!(unsolved, to_delete)
    return nothing
end


################################################################################


function compact_roots_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}}
) where {N}
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        if has_compact_roots(p)
            radius = 0
            while !has_compact_roots(p, radius)
                radius += 1
            end
            range = -radius:radius
            for x in Iterators.product(ntuple(_ -> range, Val{N}())...)
                @assert !iszero(p(x))
            end
            lines[i] = "$(p) : compact roots $(radius)"
            push!(to_delete, j)
        end
    end
    deleteat!(unsolved, to_delete)
    return nothing
end


################################################################################


function compact_univariate_projection_search!(
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}}
) where {N}
    to_delete = Int[]
    for (j, (i, p)) in enumerate(unsolved)
        if has_compact_univariate_projection(p)
            radius = 0
            while !has_compact_univariate_projection(p, radius)
                radius += 1
            end
            vars = wolfram_variables(Val{N}())
            wp = wolfram_polynomial(p, vars)
            range = -radius:radius
            for x in Iterators.product(ntuple(_ -> range, Val{N - 1}())...)
                for i = 1:N
                    rules = W"List"(W"Rule".(delete(vars, i), x)...)
                    q = weval(W"ReplaceAll"(wp, rules))
                    if (q isa Int) || (q isa WInteger)
                        @assert !iszero(q)
                    else
                        @assert q isa WExpr
                        solutions = weval(
                            W"SolveValues"(W"Equal"(q, 0), vars[i])
                        )
                        @assert solutions.head == W"List"
                        for solution in solutions.args
                            @assert !parse_bool(weval(W"IntegerQ"(solution)))
                        end
                    end
                end
            end
            lines[i] = "$(p) : compact univariate projection $(radius)"
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


function search_step!(
    search_function!,
    lines::Vector{String},
    unsolved::Vector{Pair{Int,DiophantinePolynomial{N}}},
    path::String,
    message::String
) where {N}
    old_length = length(unsolved)
    search_function!(lines, unsolved)
    new_length = length(unsolved)

    println("Solved $(old_length - new_length) equations ", message, ".")
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

    search_step!(structure_search!, lines, unsolved, path, "by structural analysis")
    search_step!(real_roots_search!, lines, unsolved, path, "by real roots")
    search_step!(compact_roots_search!, lines, unsolved, path, "by compact roots")
    search_step!(compact_univariate_projection_search!, lines, unsolved, path, "by compact univariate projection")

    return nothing
end


main(Val(parse(Int, ARGS[1])), ARGS[2])
