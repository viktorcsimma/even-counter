#ifndef ODD_PARAMETER_EXCEPTION_HPP_
#define ODD_PARAMETER_EXCEPTION_HPP_

#include <exception>

/**
 * The exception thrown when trying to add an odd number to the counter.
 */
class OddParameterException: public std::exception {};

#endif