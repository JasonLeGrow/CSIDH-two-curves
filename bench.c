#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <assert.h>

#include "u512.h"
#include "fp.h"
#include "mont.h"
#include "csidh.h"
#include "cycle.h"

#include <inttypes.h>

static __inline__ uint64_t rdtsc(void) {
	uint32_t hi, lo;
	__asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
	return lo | (uint64_t) hi << 32;
}

unsigned long its = 1024;

int main() {
	clock_t t0, t1, time = 0;
	uint64_t c0, c1, cycles = 0;
	uint64_t allticks = 0;
	ticks ticks1, ticks2;

  int8_t max[num_primes] = { 7, 14, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 18, 20, 20, 19, 17, 15, 15, 14, 14, 14, 12, 13, 12, 11, 13, 11, 11, 11, 11, 10,  9,  9,  9,  8, 8,  8,  8,  9,  8,  7,  7,  7,  7,  6,  6,  6,  6,  6,  7,  6,  7,  6,  6,  7,  6,  5,  7,  6,  6,  5,  5,  5,  5,  5,  6,  6,  5,  4};

	// calculate inverses for "elligatoring"
	// create inverse of u^2 - 1 : from 2 - 11
	for (int i = 2; i <= 10; i++) {
		fp_set(&invs_[i - 2], i);
		fp_sq1(&invs_[i - 2]);
		fp_sub2(&invs_[i - 2], &fp_1);
		fp_inv(&invs_[i - 2]);
	}

	private_key priv;
	public_key pub_r, pub_d;

	for (unsigned long i = 0; i < its; ++i) {

		csidh_private(&priv, max);

		t0 = clock();
		c0 = rdtsc();
		ticks1 = getticks();
		/**************************************/
		//assert(validate(&pub));
		action(&pub_r, &pub_d, &base, &base, &priv, max);
		/**************************************/
		ticks2 = getticks();
		allticks = allticks + elapsed(ticks2, ticks1);
		c1 = rdtsc();
		t1 = clock();
		cycles += c1 - c0;
		time += t1 - t0;
	}

	printf("iterations: %lu\n", its);
	printf("clock cycles: %" PRIu64 " (rdtsc)\n", (uint64_t) cycles / its);
	printf("clock cycles: %" PRIu64 " (getticks)\n", (uint64_t) allticks / its);

	printf("wall-clock time: %.3lf ms\n", 1000. * time / CLOCKS_PER_SEC / its);
}

