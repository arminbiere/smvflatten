/*------------------------------------------------------------------------*/
/* Copyright 1999-2013 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "prime.h"

/*------------------------------------------------------------------------*/

static unsigned primes[] = {
  3, 7, 13, 29, 59, 113, 227, 457, 911, 1823, 3643, 7283, 14563, 29129, 
  58271, 116539, 233083, 466171, 932341, 1864691, 3729379, 7458797, 
  14917583, 29835193, 59670407, 119340841, 238681669, 477363343, 
  954726701, 1909453411, 2147483647, 
};

/*------------------------------------------------------------------------*/

unsigned next_prime(unsigned a)
{
  unsigned res, l, u, i, max;

  if(a <= primes[0]) res = primes[0];
  else
    {
      max = sizeof(primes) / sizeof(unsigned);
      l = primes[0];

      for(i = 1; i < max && a > (u = primes[i]); i++)
	l = u;
      
      if(i == max) res = primes[max - 1];
      else res = (a - l < u - a) ? l : u;
    }
  
  return res;
}
