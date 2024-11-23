#ifndef FUTURE_H_
#define FUTURE_H_

/* A basic C interface for Haskell futures.
   Use the C++ wrapper class, if possible.

   These calls block until the result is ready
   and return it then.
   They throw if the calculation has been interrupted.

   For interruption, use hs_try_putmvar. */

#include "TinyHsFFI.h"
#if defined(__cplusplus)
extern "C" {
#endif

extern int getCIntFromFutureC(HsPtr a1);
extern void waitForVoidFutureC(HsPtr a1);
extern HsPtr getPtrFromFutureC(HsPtr a1);
#if defined(__cplusplus)
}
#endif

#endif
