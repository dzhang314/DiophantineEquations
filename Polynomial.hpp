#ifndef DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED

#include <cstddef> // for std::size_t
#include <vector>  // for std::vector

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


}; // struct Term


template <std::size_t NUM_VARS>
struct Polynomial : public std::vector<Term<NUM_VARS>> {}; // struct Polynomial


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
