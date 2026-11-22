/* manyan-std: the operators TLC computes in Java for its modules and for
   CommunityModules', as native operators of manyan.h. See docs/std.md. */
#ifndef MANYAN_STD_H
#define MANYAN_STD_H

#include "manyan.h"

/* Defines them all with manyan_define, once however often it is called.
   Returns 0, or -1 when out of memory. */
int manyan_std_init(void);

#endif
