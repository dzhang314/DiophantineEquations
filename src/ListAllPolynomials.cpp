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
                std::cerr << "INTERNAL ERROR: HASH COLLISION" << std::endl;
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

            if constexpr (NUM_VARS >= 2) { poly.swap_variables(0, 1); }
            const std::size_t hash_swap = poly.hash();
            if constexpr (NUM_VARS >= 2) { poly.swap_variables(0, 1); }
            if constexpr (NUM_VARS >= 1) { poly.rotate_variables_left(); }
            const std::size_t hash_rotate = poly.hash();
            if constexpr (NUM_VARS >= 1) { poly.rotate_variables_right(); }
            poly.negate();
            const std::size_t hash_negate = poly.hash();
            poly.negate();
            if constexpr (NUM_VARS >= 1) { poly.negate_variable(0); }
            const std::size_t hash_sign = poly.hash();
            if constexpr (NUM_VARS >= 1) { poly.negate_variable(0); }

            const auto find_swap = index_table.find(hash_swap);
            const auto find_rotate = index_table.find(hash_rotate);
            const auto find_negate = index_table.find(hash_negate);
            const auto find_sign = index_table.find(hash_sign);

            if ((find_swap == index_table_end) ||
                (find_rotate == index_table_end) ||
                (find_negate == index_table_end) ||
                (find_sign == index_table_end)) {
                std::cerr << "INTERNAL ERROR: HASH NOT FOUND" << std::endl;
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


template <std::size_t NUM_VARS>
void print_polynomials(T_COEFF weight) {
    const auto partitions = binary_partitions<T_EXPONENT, T_COEFF>(weight);
    for (const auto &partition : partitions) {
        const auto polynomials = unique_polynomials<NUM_VARS>(
            partition,
            [](const Polynomial<NUM_VARS> &poly) {
                return poly.uses_all_variables();
            }
        );
        for (const auto &poly : polynomials) { std::cout << poly << '\n'; }
    }
    std::cout << std::flush;
}


#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"
int main(int argc, char **argv) {

    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " num_vars weight" << std::endl;
        return EXIT_FAILURE;
    }

    for (char *num_vars_ptr = argv[1]; *num_vars_ptr; ++num_vars_ptr) {
        if (*num_vars_ptr < '0' || *num_vars_ptr > '9') {
            std::cerr << "ERROR: num_vars must be an integer between 1 and 26."
                      << std::endl;
            return EXIT_FAILURE;
        }
    }

    for (char *weight_ptr = argv[2]; *weight_ptr; ++weight_ptr) {
        if (*weight_ptr < '0' || *weight_ptr > '9') {
            std::cerr << "ERROR: weight must be a non-negative integer."
                      << std::endl;
            return EXIT_FAILURE;
        }
    }

    const std::size_t num_vars =
        static_cast<std::size_t>(std::strtoull(argv[1], nullptr, 10));
    if (num_vars < 1 || num_vars > 26) {
        std::cerr << "ERROR: num_vars must be an integer between 1 and 26."
                  << std::endl;
        return EXIT_FAILURE;
    }

    const T_COEFF weight =
        static_cast<T_COEFF>(std::strtoull(argv[2], nullptr, 10));
    if (weight < 0) {
        std::cerr << "ERROR: weight must be a non-negative integer."
                  << std::endl;
        return EXIT_FAILURE;
    }

    switch (num_vars) {
        case 1: print_polynomials<1>(weight); return EXIT_SUCCESS;
        case 2: print_polynomials<2>(weight); return EXIT_SUCCESS;
        case 3: print_polynomials<3>(weight); return EXIT_SUCCESS;
        case 4: print_polynomials<4>(weight); return EXIT_SUCCESS;
        case 5: print_polynomials<5>(weight); return EXIT_SUCCESS;
        case 6: print_polynomials<6>(weight); return EXIT_SUCCESS;
        case 7: print_polynomials<7>(weight); return EXIT_SUCCESS;
        case 8: print_polynomials<8>(weight); return EXIT_SUCCESS;
        case 9: print_polynomials<9>(weight); return EXIT_SUCCESS;
        case 10: print_polynomials<10>(weight); return EXIT_SUCCESS;
        case 11: print_polynomials<11>(weight); return EXIT_SUCCESS;
        case 12: print_polynomials<12>(weight); return EXIT_SUCCESS;
        case 13: print_polynomials<13>(weight); return EXIT_SUCCESS;
        case 14: print_polynomials<14>(weight); return EXIT_SUCCESS;
        case 15: print_polynomials<15>(weight); return EXIT_SUCCESS;
        case 16: print_polynomials<16>(weight); return EXIT_SUCCESS;
        case 17: print_polynomials<17>(weight); return EXIT_SUCCESS;
        case 18: print_polynomials<18>(weight); return EXIT_SUCCESS;
        case 19: print_polynomials<19>(weight); return EXIT_SUCCESS;
        case 20: print_polynomials<20>(weight); return EXIT_SUCCESS;
        case 21: print_polynomials<21>(weight); return EXIT_SUCCESS;
        case 22: print_polynomials<22>(weight); return EXIT_SUCCESS;
        case 23: print_polynomials<23>(weight); return EXIT_SUCCESS;
        case 24: print_polynomials<24>(weight); return EXIT_SUCCESS;
        case 25: print_polynomials<25>(weight); return EXIT_SUCCESS;
        case 26: print_polynomials<26>(weight); return EXIT_SUCCESS;
    }

    return EXIT_FAILURE;
}
#pragma clang diagnostic pop
