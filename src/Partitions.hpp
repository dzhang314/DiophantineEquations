#ifndef DIOPHANTINE_EQUATIONS_PARTITIONS_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_PARTITIONS_HPP_INCLUDED

#include <utility> // for std::move, std::pair, std::make_pair
#include <vector>  // for std::vector

namespace DiophantineEquations {


/**
 * Given a list of non-negative integers, compute another list of non-negative
 * integers, having the same sum as the given list, which is next smallest in
 * lexicographic order. The result is returned in-place by modifying the input.
 */
template <typename T>
constexpr bool decrement_partition(std::vector<T> &partition) noexcept {

    constexpr T ZERO = static_cast<T>(0);
    constexpr T ONE = static_cast<T>(1);
    using index_t = typename std::vector<T>::size_type;
    const index_t n = partition.size();

    // Partitions of length 0 and 1 are unique, so they cannot be decremented.
    if (n <= 1) { return false; }

    // If the next-to-last element is positive, decrement it and increment the
    // final element.
    if (partition[n - 2] > 0) {
        partition[n - 2] -= ONE;
        partition[n - 1] += ONE;
        return true;
    }

    // Otherwise, scan backwards until we find a positive element.
    for (index_t i = n - 2; i > 0; --i) {
        // If we find one, decrement it and move the value of the final element
        // backwards into the next element.
        if (partition[i - 1] > 0) {
            partition[i - 1] -= ONE;
            partition[i] = partition[n - 1] + ONE;
            partition[n - 1] = ZERO;
            return true;
        }
    }

    // If we find no positive elements, then we already have the
    // lexicographically smallest partition, which cannot be decremented.
    return false;
}


/**
 * Given integers `i` and `k`, compute and return a list of all possible ways
 * to express `k` as a sum of powers of two, up to and including `1 << i`.
 *
 * The result is encoded as a collection of lists of pairs, as follows:
 * Each element `(m, n)` of an output list represents `m` copies of `1 << n`.
 * For example, `{(3, 1), (1, 4), (0, 1)}` represents `{8, 2, 2, 2, 2, 1}`.
 */
template <typename T_INDEX, typename T_VALUE>
constexpr std::vector<std::vector<std::pair<T_INDEX, T_VALUE>>>
binary_partitions(T_INDEX i, T_VALUE k) noexcept {

    // It is impossible for a sum of powers of two to be negative.
    if (k < 0) { return {}; }

    // Zero is uniquely expressed by the empty sum.
    if (k == 0) { return {{}}; }

    // Do not handle negative powers of two.
    if (i < 0) { return {}; }

    // Base case: When `i == 0`, the only possible result is to express `k`
    // as a sum of `k` copies of `1`.
    if (i == 0) { return {{std::make_pair(static_cast<T_INDEX>(0), k)}}; }

    // Recursive case: Iterate over all possible values for the number of
    // occurrences of `1 << i` in the resulting partition.
    const T_VALUE value = static_cast<T_VALUE>(1 << i);
    std::vector<std::vector<std::pair<T_INDEX, T_VALUE>>> result;
    for (T_VALUE first = k / value; first > 0; --first) {
        // Recursively compute all possible partitions of the remaining value
        // using powers of two smaller than `1 << i`.
        const std::vector<std::vector<std::pair<T_INDEX, T_VALUE>>> tails =
            binary_partitions<T_INDEX, T_VALUE>(i - 1, k - first * value);
        for (const std::vector<std::pair<T_INDEX, T_VALUE>> &tail : tails) {
            std::vector<std::pair<T_INDEX, T_VALUE>> partition;
            partition.emplace_back(i, first);
            partition.insert(partition.end(), tail.begin(), tail.end());
            result.push_back(std::move(partition));
        }
    }

    const std::vector<std::vector<std::pair<T_INDEX, T_VALUE>>> rest =
        binary_partitions<T_INDEX, T_VALUE>(i - 1, k);
    result.insert(result.end(), rest.begin(), rest.end());
    return result;
}


static_assert(binary_partitions<int, int>(-1, -1).size() == 0);
static_assert(binary_partitions<int, int>(0, -1).size() == 0);
static_assert(binary_partitions<int, int>(1, -1).size() == 0);
static_assert(binary_partitions<int, int>(-1, 0).size() == 1);
static_assert(binary_partitions<int, int>(0, 0).size() == 1);
static_assert(binary_partitions<int, int>(1, 0).size() == 1);
static_assert(binary_partitions<int, int>(-1, 1).size() == 0);
static_assert(binary_partitions<int, int>(0, 1).size() == 1);
static_assert(binary_partitions<int, int>(1, 1).size() == 1);


/**
 * Given an integer `k`, compute and return a list of all possible ways
 * to express `k` as a sum of powers of two.
 *
 * The result is encoded as a collection of lists of pairs, as follows:
 * Each element `(m, n)` of an output list represents `m` copies of `1 << n`.
 * For example, `{(3, 1), (1, 4), (0, 1)}` represents `{8, 2, 2, 2, 2, 1}`.
 */
template <typename T_INDEX, typename T_VALUE>
constexpr std::vector<std::vector<std::pair<T_INDEX, T_VALUE>>>
binary_partitions(T_VALUE k) noexcept {

    // It is impossible for a sum of powers of two to be negative.
    if (k < 0) { return {}; }

    // Zero is uniquely expressed by the empty sum.
    if (k == 0) { return {{}}; }

    // Find the largest value of `i` such that `1 << i` is at most `k`.
    T_INDEX i = static_cast<T_INDEX>(0);
    while (static_cast<T_VALUE>(1 << i) <= k) { ++i; }
    return binary_partitions<T_INDEX, T_VALUE>(--i, k);
}


static_assert(binary_partitions<int, int>(-1).size() == 0);
static_assert(binary_partitions<int, int>(0).size() == 1);
static_assert(binary_partitions<int, int>(1).size() == 1);
static_assert(binary_partitions<int, int>(2).size() == 2);
static_assert(binary_partitions<int, int>(3).size() == 2);
static_assert(binary_partitions<int, int>(4).size() == 4);
static_assert(binary_partitions<int, int>(5).size() == 4);


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_PARTITIONS_HPP_INCLUDED
