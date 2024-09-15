#ifndef REAL_BASE_TYPE_HPP_
#define REAL_BASE_TYPE_HPP_

// Represents the possible base types of the real type.
// It cannot conflict with the Rational value type;
// hence the suffix.
enum RealBaseType {DyadicBase, RationalBase};

// Maps C strings to corresponding RealBaseTypes.
// Throws if there is no equivalent.
RealBaseType stringToRealBaseType(const char* name);

#endif