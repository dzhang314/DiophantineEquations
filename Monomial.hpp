#ifndef DIOPHANTINE_EQUATIONS_MONOMIAL_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_MONOMIAL_HPP_INCLUDED

#include <array>   // for std::array
#include <compare> // for operator<=>
#include <cstddef> // for std::size_t
#include <cstdint> // for std::intNN_t, std::uintNN_t
#include <vector>  // for std::vector

namespace DiophantineEquations {


using T_COEFF = std::int16_t;
using T_EXPONENT = std::uint16_t;


template <std::size_t NUM_VARS>
struct Monomial {


    std::array<T_EXPONENT, NUM_VARS> exponents;


    explicit constexpr Monomial() noexcept
        : exponents() {
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            exponents[i] = static_cast<T_EXPONENT>(0);
        }
    }


    constexpr bool operator<=>(const Monomial &) const noexcept = default;


    constexpr T_EXPONENT get_exponent(std::size_t i) const noexcept {
        return exponents[i];
    }


    constexpr void set_exponent(std::size_t i, T_EXPONENT value) noexcept {
        exponents[i] = value;
    }


    /**
     * Compute and return a list of all possible monomials of total degree
     * `degree` in `NUM_VARS` variables. The returned list is sorted in
     * degrevlex order.
     */
    static constexpr std::vector<Monomial> all_monomials(T_EXPONENT degree
    ) noexcept {
        std::vector<Monomial<NUM_VARS>> result;
        if constexpr (NUM_VARS == 0) {
            if (degree == 0) { result.emplace_back(); }
        } else if constexpr (NUM_VARS == 1) {
            Monomial<1> monomial;
            monomial.set_exponent(0, degree);
            result.push_back(monomial);
        } else {
            // To produce monomials in degrevlex order, iterate over
            // possible values of the exponent of the *last* variable.
            for (T_EXPONENT last = 0; last <= degree; ++last) {
                // Recursively compute all possible monomials of the
                // remaining total degree in `NUM_VARS - 1` variables.
                const std::vector<Monomial<NUM_VARS - 1>> heads =
                    Monomial<NUM_VARS - 1>::all_monomials(degree - last);
                for (const Monomial<NUM_VARS - 1> &head : heads) {
                    Monomial<NUM_VARS> monomial;
                    for (std::size_t i = 0; i < NUM_VARS - 1; ++i) {
                        monomial.set_exponent(i, head.get_exponent(i));
                    }
                    monomial.set_exponent(NUM_VARS - 1, last);
                    result.push_back(monomial);
                }
            }
        }
        return result;
    }


}; // struct Monomial


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_MONOMIAL_HPP_INCLUDED
