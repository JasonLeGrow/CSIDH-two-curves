#include <stdlib.h>
#include <stdio.h>
#include <string.h>
//#include <unistd.h>
#include <time.h>
#include <assert.h>

#include "u512.h"
#include "fp.h"
#include "mont.h"
#include "csidh.h"
#include "cycle.h"

void u512_print(u512 const *x) {
  for (size_t i = 63; i < 64; --i)
    printf("%02hhx", i[(unsigned char *) x->c]);
}

void fp_print(fp const *x) {
  u512 y;
  fp_dec(&y, x);
  u512_print(&y);
}

int main() {

  clock_t t0, t1;

  int8_t max[num_primes] = { 7, 14, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 18, 20, 20, 19, 17, 15, 15, 14, 14, 14, 12, 13, 12, 11, 13, 11, 11, 11, 11, 10,  9,  9,  9,  8, 8,  8,  8,  9,  8,  7,  7,  7,  7,  6,  6,  6,  6,  6,  7,  6,  7,  6,  6,  7,  6,  5,  7,  6,  6,  5,  5,  5,  5,  5,  6,  6,  5,  4};

  private_key priv_alice, priv_bob;
  public_key pub_alice_r, pub_alice_d, pub_bob_r, pub_bob_d;
  public_key shared_alice_r, shared_alice_d, shared_bob_r, shared_bob_d;


  // calculate inverses for "elligatoring"
  // compute inverse of u^2 - 1 : from u in {2,..,10}
  for (int i = 2; i <= 10; i++) {
    fp_set(&invs_[i - 2], i);
    fp_sq1(&invs_[i - 2]);
    fp_sub2(&invs_[i - 2], &fp_1);
    fp_inv(&invs_[i - 2]);
  }

  t0 = clock();
//  csidh_private_zero(&priv_alice, max);
  csidh_private(&priv_alice, max);
  t1 = clock();

  printf("Alice's private key   (%7.3lf ms):\n  ", 1000. * (t1 - t0) / CLOCKS_PER_SEC);
  for (size_t i = 0; i < sizeof(priv_alice); ++i)
    printf("%01x", i[(int8_t *) &priv_alice]);
  printf("\n\n");

  t0 = clock();
// csidh_private_zero(&priv_bob, max);
  csidh_private(&priv_bob, max);
  t1 = clock();

  printf("Bob's private key     (%7.3lf ms):\n  ", 1000. * (t1 - t0) / CLOCKS_PER_SEC);
  for (size_t i = 0; i < sizeof(priv_alice); ++i)
    printf("%01x", i[(int8_t *) &priv_bob]);
  printf("\n\n");

  //assert(csidh(&pub_alice_r, &pub_alice_d, &base, &base, &priv_alice, max));

  t0 = clock();
  assert(csidh(&pub_alice_r, &pub_alice_d, &base, &base, &priv_alice, max));
  t1 = clock();

  printf("Alice's public key (including validation) (%7.3lf ms):\n  ", 1000. * (t1 - t0) / CLOCKS_PER_SEC);
  for (size_t i = 0; i < sizeof(pub_alice_r); ++i)
    printf("%02hhx", i[(uint8_t *) &pub_alice_r]);
  printf("\n");
  for (size_t i = 0; i < sizeof(pub_alice_d); ++i)
    printf("%02hhx", i[(uint8_t *) &pub_alice_d]);
  printf("\n\n");

  t0 = clock();
  assert(csidh(&pub_bob_r, &pub_bob_d, &base, &base, &priv_bob, max));
  t1 = clock();

  printf("Bob's public key (including validation) (%7.3lf ms):\n  ", 1000. * (t1 - t0) / CLOCKS_PER_SEC);
  for (size_t i = 0; i < sizeof(pub_bob_r); ++i)
    printf("%02hhx", i[(uint8_t *) &pub_bob_r]);
  printf("\n");
  for (size_t i = 0; i < sizeof(pub_bob_d); ++i)
    printf("%02hhx", i[(uint8_t *) &pub_bob_d]);
  printf("\n\n");


  t0 = clock();
  assert(csidh(&shared_alice_r, &shared_alice_d, &pub_bob_r, &pub_bob_d, &priv_alice, max));
  t1 = clock();

  printf("Alice's shared secret (including validation) (%7.3lf ms):\n  ", 1000. * (t1 - t0) / CLOCKS_PER_SEC);
  for (size_t i = 0; i < sizeof(shared_alice_r); ++i)
    printf("%02hhx", i[(uint8_t *) &shared_alice_r]);
  printf("\n");
  for (size_t i = 0; i < sizeof(shared_alice_d); ++i)
    printf("%02hhx", i[(uint8_t *) &shared_alice_d]);
  printf("\n\n");

  t0 = clock();
  assert(csidh(&shared_bob_r, &shared_bob_d, &pub_alice_r, &pub_alice_d, &priv_bob, max));
  t1 = clock();

  printf("Bob's shared secret (including validation) (%7.3lf ms):\n  ", 1000. * (t1 - t0) / CLOCKS_PER_SEC);
  for (size_t i = 0; i < sizeof(shared_bob_r); ++i)
    printf("%02hhx", i[(uint8_t *) &shared_bob_r]);
  printf("\n");
  for (size_t i = 0; i < sizeof(shared_bob_d); ++i)
    printf("%02hhx", i[(uint8_t *) &shared_bob_d]);
  printf("\n\n");




  if (memcmp(&shared_alice_r, &shared_bob_r, sizeof(public_key)) || memcmp(&shared_alice_d, &shared_bob_d, sizeof(public_key)))
    printf("\x1b[31mNOT EQUAL! :(\x1b[0m\n");
  else
    printf("\x1b[32mequal :)\x1b[0m\n");
  printf("\n");

}
