#ifndef ACORN_H_
#define ACORN_H_

#include "TinyHsFFI.h"
#if defined(__cplusplus)
extern "C" {
#endif

// from the FFI

// Initialises an AppState with base type Dyadic
// and returns a StablePtr to it.
extern HsStablePtr initAppInt(void);

// Returns the counter value stored in the AppState.
extern int getCounterValueInt(HsStablePtr appState);

// Increases the value of the counter with the given number.
// Returns -1 if the value with which to increment is odd (in which case, it leaves the counter value unchanged);
// and 0 on success.
extern int incrementWithInt(HsStablePtr appState, int toAdd);

// Increases the counter by 2 every second
// for the given number of seconds
// or until getting interrupted.
// Returns -1 if interrupted and 0 otherwise.
// This shows how interruptible calculations
// can be implemented.
extern int increaseContinuouslyInt(HsStablePtr appState, int duration);

// Frees the StablePtr to the CalcState object,
// as this could not be done from the C side.
extern void destructAppInt(HsStablePtr calcState);

// This is written by ourselves in src/acornInterruptEvaluation.c.
// It interrupts a running calculation
// by opening and incrementing the "/AcornInterruptSemaphore" POSIX semaphore (on Unix)
// or opening and triggering the "AcornInterruptEvent" event (on Windows).
extern void acornInterruptEvaluation();

#if defined(__cplusplus)
}
#endif

#endif
