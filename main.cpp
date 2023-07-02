#include "Monomial.hpp"
#include "Partitions.hpp"
#include "Polynomial.hpp"
#include "PolynomialIterator.hpp"

#include <cstdlib>
#include <iostream>
#include <unordered_map>

using namespace DiophantineEquations;


template <std::size_t N>
std::vector<std::size_t> connected_components(
    const std::vector<std::array<std::size_t, N>> &adjacency_lists
) {
    std::vector<std::size_t> result;

    // Initially, no vertex has been visited yet.
    std::vector<bool> visited(adjacency_lists.size(), false);

    // Iterate over all vertices in order.
    for (std::size_t i = 0; i < adjacency_lists.size(); ++i) {

        // Whenever we come across a vertex not yet visited,
        // we have discovered the origin of a new connected component.
        if (!visited[i]) {

            // Record the origin of the new connected component.
            result.push_back(i);
            visited[i] = true;

            // Perform a depth-first search from this origin.
            std::vector<std::size_t> stack;
            for (const std::size_t j : adjacency_lists[i]) {
                stack.push_back(j);
            }
            while (!stack.empty()) {
                const std::size_t j = stack.back();
                stack.pop_back();
                if (!visited[j]) {
                    visited[j] = true;
                    for (const std::size_t k : adjacency_lists[j]) {
                        if (!visited[k]) { stack.push_back(k); }
                    }
                }
            }
        }
    }
    return result;
}


template <std::size_t NUM_VARS, typename F>
std::vector<Polynomial<NUM_VARS>> unique_polynomials(
    const std::vector<std::pair<T_EXPONENT, T_COEFF>> &partition,
    const F &selector
) noexcept {

    // Build index table.
    std::unordered_map<std::size_t, std::size_t> index_table;
    PolynomialIterator<NUM_VARS> polynomial_iterator(partition);
    std::size_t count = 0;
    do {
        const Polynomial<NUM_VARS> poly = polynomial_iterator.get_polynomial();
        if (selector(poly)) {
            const std::size_t hash = poly.hash();
            if (index_table.contains(hash)) {
                std::cerr << "ERROR: HASH COLLISION" << std::endl;
                std::exit(EXIT_FAILURE);
            }
            index_table.insert({hash, count++});
        }
    } while (polynomial_iterator.increment());

    // Construct adjacency lists for isomorphism classes.
    std::vector<std::array<std::size_t, 4>> adjacency_lists;
    const auto index_table_end = index_table.end();
    polynomial_iterator.reset();
    do {
        Polynomial<NUM_VARS> poly = polynomial_iterator.get_polynomial();
        if (selector(poly)) {

            poly.swap_variables(0, 1);
            const std::size_t hash_swap = poly.hash();
            poly.swap_variables(0, 1);
            poly.rotate_variables_left();
            const std::size_t hash_rotate = poly.hash();
            poly.rotate_variables_right();
            poly.negate();
            const std::size_t hash_negate = poly.hash();
            poly.negate();
            poly.negate_variable(0);
            const std::size_t hash_sign = poly.hash();
            poly.negate_variable(0);

            const auto find_swap = index_table.find(hash_swap);
            const auto find_rotate = index_table.find(hash_rotate);
            const auto find_negate = index_table.find(hash_negate);
            const auto find_sign = index_table.find(hash_sign);

            if ((find_swap == index_table_end) ||
                (find_rotate == index_table_end) ||
                (find_negate == index_table_end) ||
                (find_sign == index_table_end)) {
                std::cerr << "ERROR: HASH NOT FOUND" << std::endl;
                std::exit(EXIT_FAILURE);
            }

            adjacency_lists.push_back(
                {find_swap->second,
                 find_rotate->second,
                 find_negate->second,
                 find_sign->second}
            );
        }
    } while (polynomial_iterator.increment());

    // Choose one representative from each isomorphism class.
    const std::vector<std::size_t> representative_indices =
        connected_components(adjacency_lists);
    auto representative_iterator = representative_indices.begin();
    const auto representative_indices_end = representative_indices.end();
    std::vector<Polynomial<NUM_VARS>> result;
    polynomial_iterator.reset();
    count = 0;
    do {
        Polynomial<NUM_VARS> poly = polynomial_iterator.get_polynomial();
        if (selector(poly)) {
            if (count++ == *representative_iterator) {
                result.push_back(std::move(poly));
                if (++representative_iterator == representative_indices_end) {
                    break;
                }
            }
        }
    } while (polynomial_iterator.increment());

    return result;
}


int main() {

    for (T_COEFF weight = 0; weight <= 30; ++weight) {
        std::cout << weight << std::endl;
        const auto partitions = binary_partitions<T_EXPONENT, T_COEFF>(weight);
        for (const auto &partition : partitions) {
            const auto polynomials =
                unique_polynomials<4>(partition, [](const Polynomial<4> &poly) {
                    return poly.uses_all_variables() &&
                           poly.has_constant_term() &&
                           !poly.has_linear_variable() &&
                           !poly.has_root_in_radius<std::intmax_t>(1) &&
                           !poly.has_root_in_radius<std::intmax_t>(2) &&
                           !poly.has_root_in_radius<std::intmax_t>(3) &&
                           !poly.has_root_in_radius<std::intmax_t>(4) &&
                           !poly.has_root_in_radius<std::intmax_t>(5) &&
                           !poly.has_root_in_radius<std::intmax_t>(6) &&
                           !poly.has_root_in_radius<std::intmax_t>(7) &&
                           !poly.has_root_in_radius<std::intmax_t>(8) &&
                           !poly.has_root_in_radius<std::intmax_t>(9) &&
                           !poly.has_root_in_radius<std::intmax_t>(10);
                });
            for (const auto &poly : polynomials) {
                std::cout << poly << std::endl;
            }
        }
    }
}
