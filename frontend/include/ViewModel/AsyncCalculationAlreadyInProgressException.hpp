#ifndef ODD_PARAMETER_EXCEPTION_HPP_
#define ODD_PARAMETER_EXCEPTION_HPP_

#include <exception>

/**
 * The exception thrown when trying to launch an asynchronous calculation on the view model
 * while one is already running.
 */
class AsyncCalculationAlreadyInProgressException: public std::exception {};

#endif
