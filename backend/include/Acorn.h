#ifndef ACORN_H_
#define ACORN_H_

#include "TinyHsFFI.h"
#if defined(__cplusplus)
extern "C" {
#endif

// from the FFI

// Initialises an AppState with base type Dyadic
// and returns a StablePtr to it.
extern HsStablePtr initAppInteger(void);

// Returns the counter value stored in the AppState.
extern int getCounterValueInteger(HsStablePtr appState);

// Increases the value of the counter with the given number.
// Returns -1 if the value with which to increment is odd (in which case, it leaves the counter value unchanged);
// and 0 on success.
extern int incrementInteger(HsStablePtr appState, int toAdd);

// Increases the counter by 2 every second
// for the given number of seconds
// or until getting interrupted,
// writes a Future into the pointer specified,
// that returns the value of the counter.
// This shows how asynchronous calculations
// can be implemented.
extern void increaseContinuouslyIntegerAsyncC(HsStablePtr appState, int duration, HsPtr future);

// This is written by ourselves in src/acornInterruptEvaluation.c.
// It interrupts a running calculation
// by opening and incrementing the "/AcornInterruptSemaphore" POSIX semaphore (on Unix)
// or opening and triggering the "AcornInterruptEvent" event (on Windows).
extern void acornInterruptEvaluation();

#if defined(__cplusplus)
}
#endif

#endif
