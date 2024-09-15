#ifndef RESULT_TYPE_HPP_
#define RESULT_TYPE_HPP_

// An enum representing the four possible types of a value.
enum ResultType {Bool, Integer, Rational, Real};

// Maps a C string to the corresponding ResultType.
// Throws if the name is unknown.
ResultType stringToResultType(const char* name);

#endif