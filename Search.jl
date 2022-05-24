using MathLink
using Singular

push!(LOAD_PATH, @__DIR__)
using SystematicDiophantineEquations
using SystematicDiophantineEquations: shell, positive_orthant,
    has_root, has_root_modulo, canonical_variables

function has_unbounded_roots(p::Polynomial{N}) where {N}
    vars = MathLink.WSymbol.(canonical_variables(N))
    terms = [
        W"Times"(c, W"Apply"(W"Times", W"Power"(vars, m)))
        for (c, m) in p
    ]
    eqn = weval(W"Equal"(W"Plus"(terms...), 0))
    norm = W"Plus"([W"Times"(v, v) for v in vars]...)
    problem = W"ForAll"(W"t", W"Exists"(vars,
        W"And"(eqn, W"Greater"(norm, W"t"))
    ))
    result = weval(W"Resolve"(problem, W"Reals"))
    if result == W"True"
        return true
    elseif result == W"False"
        return false
    else
        error()
    end
end

function main(::Val{N}, max_root::Int, max_modulus::Int) where {N}
    trial_roots = reduce(vcat, shell(Val{N}(), k) for k = 0 : max_root)
    orthants = [positive_orthant(Val{N}(), k) for k = 1 : max_modulus]
    height = 0
    while true
        println("================================================= ", height)
        flush(stdout)
        for p in dedup(nontrivial_polynomials(Val{N}(), height))
            if has_root(p, trial_roots)
                continue
            end
            found = false
            for k = 2 : max_modulus
                if !has_root_modulo(p, k, orthants[k])
                    found = true
                    break
                end
            end
            if found
                continue
            end
            if !has_unbounded_roots(p)
                continue
            end
            println(p, " | ", to_degrevlex_string(p))
            flush(stdout)
        end
        height += 1
    end
end

main(Val{parse(Int, ARGS[1])}(), parse(Int, ARGS[2]), parse(Int, ARGS[3]))
