#ifndef DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED

#include <algorithm> // for std::sort
#include <array>     // for std::array
#include <cstddef>   // for std::size_t
#include <ostream>   // for std::ostream
#include <utility>   // for std::pair, std::make_pair
#include <vector>    // for std::vector

#include "Monomial.hpp" // for Monomial, T_COEFF

namespace DiophantineEquations {


template <std::size_t NUM_VARS>
struct Term {


    Monomial<NUM_VARS> monom;
    T_COEFF coeff;


    explicit constexpr Term(
        const Monomial<NUM_VARS> &monomial, T_COEFF coefficient
    )
        : monom(monomial)
        , coeff(coefficient) {}


    constexpr void negate() noexcept { coeff = -coeff; }


    constexpr void negate_variable(std::size_t i) noexcept {
        if (monom.get_exponent(i) & 1) { coeff = -coeff; }
    }


}; // struct Term


template <std::size_t NUM_VARS>
struct Polynomial : public std::vector<Term<NUM_VARS>> {


    constexpr bool uses_variable(std::size_t i) const noexcept {
        for (const Term<NUM_VARS> &term : *this) {
            if (term.monom.get_exponent(i) != 0) { return true; }
        }
        return false;
    }


    constexpr bool uses_all_variables() const noexcept {
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            if (!uses_variable(i)) { return false; }
        }
        return true;
    }


    constexpr bool has_constant_term() const noexcept {
        for (const Term<NUM_VARS> &term : *this) {
            if (term.monom.is_constant()) { return true; }
        }
        return false;
    }


    constexpr bool has_linear_variable(std::size_t i) const noexcept {
        for (const Term<NUM_VARS> &term : *this) {
            if (!(term.monom.is_constant_in(i) || term.monom.is_linear_in(i))) {
                return false;
            }
        }
        return true;
    }


    constexpr bool has_linear_variable() const noexcept {
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            if (has_linear_variable(i)) { return true; }
        }
        return false;
    }


    constexpr void swap_variables(std::size_t i, std::size_t j) noexcept {
        for (Term<NUM_VARS> &term : *this) { term.monom.swap_variables(i, j); }
    }


    constexpr void rotate_variables_left() noexcept {
        for (Term<NUM_VARS> &term : *this) {
            term.monom.rotate_variables_left();
        }
    }


    constexpr void rotate_variables_right() noexcept {
        for (Term<NUM_VARS> &term : *this) {
            term.monom.rotate_variables_right();
        }
    }


    constexpr void negate() noexcept {
        for (Term<NUM_VARS> &term : *this) { term.negate(); }
    }


    constexpr void negate_variable(std::size_t i) noexcept {
        for (Term<NUM_VARS> &term : *this) { term.negate_variable(i); }
    }


    constexpr std::vector<std::pair<std::array<T_EXPONENT, NUM_VARS>, T_COEFF>>
    canonical_form() const noexcept {
        std::vector<std::pair<std::array<T_EXPONENT, NUM_VARS>, T_COEFF>>
            result;
        for (const Term<NUM_VARS> &term : *this) {
            result.emplace_back(term.monom.exponents, term.coeff);
        }
        std::sort(result.begin(), result.end());
        return result;
    }


}; // struct Polynomial


template <std::size_t NUM_VARS>
std::ostream &
operator<<(std::ostream &os, const Polynomial<NUM_VARS> &polynomial) {

    static_assert(NUM_VARS <= 26);

    if (polynomial.empty()) {
        os << '0';
        return os;
    }

    bool first = true;
    for (const Term<NUM_VARS> &term : polynomial) {

        const bool sign = (term.coeff < 0);
        if (first) {
            if (sign) { os << '-'; }
            first = false;
        } else {
            os << (sign ? " - " : " + ");
        }

        const T_COEFF abs_coeff = sign ? -term.coeff : term.coeff;
        if ((abs_coeff != 1) || term.monom.is_constant()) {
            os << static_cast<long long int>(abs_coeff);
        }

        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            const T_EXPONENT exponent = term.monom.get_exponent(i);
            if (exponent != 0) {
                os << static_cast<char>(((NUM_VARS <= 3) ? 'x' : 'a') + i);
                if (exponent != 1) {
                    os << '^';
                    os << static_cast<long long int>(exponent);
                }
            }
        }
    }
    return os;
}


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
