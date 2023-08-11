#ifndef DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED

#include <cstddef> // for std::size_t
#include <ostream> // for std::ostream
#include <vector>  // for std::vector

#include "Monomial.hpp" // for Monomial, T_COEFF

namespace DiophantineEquations {


template <std::size_t NUM_VARS>
struct Term {


public: /////////////////////////////////////////////////////// MEMBER VARIABLES


    Monomial<NUM_VARS> monom;
    T_COEFF coeff;


public: //////////////////////////////////////////////////////////// CONSTRUCTOR


    explicit constexpr Term(
        const Monomial<NUM_VARS> &monomial, T_COEFF coefficient
    )
        : monom(monomial)
        , coeff(coefficient) {}


public: //////////////////////////////////////////////////// SYMMETRY OPERATIONS


    constexpr void negate() noexcept { coeff = -coeff; }


    constexpr void negate_variable(std::size_t i) noexcept {
        if (monom.get_exponent(i) & 1) { coeff = -coeff; }
    }


public: //////////////////////////////////////////////////////////////// HASHING


    constexpr std::size_t hash() const noexcept {
        constexpr std::size_t SHIFT =
            static_cast<std::size_t>(0x9E3779B97F4A7C15ULL);
        constexpr std::size_t MULTIPLIER =
            static_cast<std::size_t>(0x517CC1B727220A94ULL);
        std::size_t result = static_cast<std::size_t>(coeff) * MULTIPLIER;
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            result ^=
                static_cast<std::size_t>(monom.get_exponent(i)) * MULTIPLIER +
                SHIFT + (result << 6) + (result >> 2);
        }
        return result;
    }


}; // struct Term


static_assert(sizeof(Term<1>) == sizeof(T_EXPONENT) + sizeof(T_COEFF));
static_assert(sizeof(Term<2>) == 2 * sizeof(T_EXPONENT) + sizeof(T_COEFF));
static_assert(sizeof(Term<3>) == 3 * sizeof(T_EXPONENT) + sizeof(T_COEFF));
static_assert(sizeof(Term<4>) == 4 * sizeof(T_EXPONENT) + sizeof(T_COEFF));


template <std::size_t NUM_VARS>
class Polynomial : public std::vector<Term<NUM_VARS>> {


public: /////////////////////////////////////////////////////// PROPERTY TESTING


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


public: //////////////////////////////////////////////////// SYMMETRY OPERATIONS


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


public: //////////////////////////////////////////////////////////////// HASHING


    constexpr std::size_t hash() const noexcept {
        std::size_t result = 0;
        for (const Term<NUM_VARS> &term : *this) { result += term.hash(); }
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
            os << static_cast<int>(abs_coeff);
        }

        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            const T_EXPONENT exponent = term.monom.get_exponent(i);
            if (exponent != 0) {
                os << static_cast<char>(((NUM_VARS <= 3) ? 'x' : 'a') + i);
                if (exponent != 1) {
                    os << '^';
                    os << static_cast<int>(exponent);
                }
            }
        }
    }
    return os;
}


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
