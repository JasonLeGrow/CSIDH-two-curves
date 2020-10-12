#include <string.h>
#include <assert.h>
#include <stdio.h>

#include "csidh.h"
#include "rng.h"

const unsigned primes[num_primes] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 587};

uint8_t elligator_index = 0;
const u512 four_sqrt_p = { { 0x85e2579c786882cf, 0x4e3433657e18da95, 0x850ae5507965a0b3, 0xa15bc4e676475964, } };

const public_key base = { 0 }; /* A = 0 */

/* get priv[pos] in constant time  */
uint32_t lookup(size_t pos, int8_t const *priv)
{
  int b;
  int8_t r = priv[0];
  for(size_t i=1;i<num_primes;i++)
  {
    b = isequal(i, pos);
    //ISEQUAL(i, pos, b);
    //b = (uint8_t)(1-((-(i ^ pos)) >> 31));
    cmov(&r, &priv[i], b);
    //CMOV(&r, &priv[i], b);
  }
  return r;
}

/* check if a and b are equal in constant time  */
uint32_t isequal(uint32_t a, uint32_t b)
{
  //size_t i;
  uint32_t r = 0;
  unsigned char *ta = (unsigned char *)&a;
  unsigned char *tb = (unsigned char *)&b;
  r = (ta[0] ^ tb[0]) | (ta[1] ^ tb[1]) | (ta[2] ^ tb[2]) |  (ta[3] ^ tb[3]);
  r = (-r);
  r = r >> 31;
  return (int)(1-r);
}


/* decision bit b has to be either 0 or 1 */
void cmov(int8_t *r, const int8_t *a, uint32_t b)
{
  uint32_t t;
  b = -b; /* Now b is either 0 or 0xffffffff */
  t = (*r ^ *a) & b;
  *r ^= t;
}


void csidh_private(private_key *priv, const int8_t *max_exponent) {
  memset(&priv->e, 0, sizeof(priv->e));
  for (size_t i = 0; i < num_primes;) {
    int8_t buf[64];
    randombytes(buf, sizeof(buf));
    for (size_t j = 0; j < sizeof(buf); ++j) {
      if (buf[j] <= max_exponent[i] && buf[j] >= 0) {
    priv->e[i] = lookup(j, buf);
    if (++i >= num_primes)
      break;
      }
    }
  }
}

/* compute [(p+1)/l] P for all l in our list of primes. */
/* divide and conquer is much faster than doing it naively,
 * but uses more memory. */
static void cofactor_multiples(proj *P, const proj *A, size_t lower,
    size_t upper) {
  assert(lower < upper);

  if (upper - lower == 1)
    return;

  size_t mid = lower + (upper - lower + 1) / 2;

  u512 cl = u512_1, cu = u512_1;
  for (size_t i = lower; i < mid; ++i)
    u512_mul3_64(&cu, &cu, primes[i]);
  for (size_t i = mid; i < upper; ++i)
    u512_mul3_64(&cl, &cl, primes[i]);

  xMUL(&P[mid], A, &P[lower], &cu);
  xMUL(&P[lower], A, &P[lower], &cl);

  cofactor_multiples(P, A, lower, mid);
  cofactor_multiples(P, A, mid, upper);
}

/* never accepts invalid keys. */
bool validate(public_key const *in) {
  const proj A = { in->A, fp_1 };

  do {

    proj P[num_primes];
    fp_random(&P->x);
    P->z = fp_1;

    /* maximal 2-power in p+1 */
    xDBL(P, &A, P);
    xDBL(P, &A, P);

    cofactor_multiples(P, &A, 0, num_primes);

    u512 order = u512_1;

    for (size_t i = num_primes - 1; i < num_primes; --i) {

      /* we only gain information if [(p+1)/l] P is non-zero */
      if (memcmp(&P[i].z, &fp_0, sizeof(fp))) {

    u512 tmp;
    u512_set(&tmp, primes[i]);
    xMUL(&P[i], &A, &P[i], &tmp);

    if (memcmp(&P[i].z, &fp_0, sizeof(fp)))
      /* P does not have order dividing p+1. */
      return false;

    u512_mul3_64(&order, &order, primes[i]);

    if (u512_sub3(&tmp, &four_sqrt_p, &order)) /* returns borrow */
      /* order > 4 sqrt(p), hence definitely supersingular */
      return true;
      }
    }

    /* P did not have big enough order to prove supersingularity. */
  } while (1);
}

/* compute x^3 + Ax^2 + x */
static void montgomery_rhs(fp *rhs, fp const *A, fp const *x) {
  fp tmp;
  *rhs = *x;
  fp_sq1(rhs);
  fp_mul3(&tmp, A, x);
  fp_add2(rhs, &tmp);
  fp_add2(rhs, &fp_1);
  fp_mul2(rhs, x);
}


/* generates a curve point with suitable field of definition for y-coordinate */
void elligator(fp * x, const fp *A, bool sign, uint8_t index) {

  fp legendre_symbol;
  // v = A/(u^2 − 1)
  fp_set(x, 0);
  fp_add2(x, &invs_[index]);
  fp_mul2(x, A);
  // Compute the Legendre symbol
  montgomery_rhs(&legendre_symbol, A, x);
  // Compute x as v if e = s
  if(fp_issquare(&legendre_symbol)!=sign){
    // otherwise − v − A
    fp_add2(x, A);
    fp_sub3(x, &fp_0, x);

  }

}
void assign_bounds(int8_t *bound){
  int8_t vals[74] = {7, 14, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 18, 20, 20, 19, 17, 15, 15, 14, 14, 14, 12, 13, 12, 11, 13, 11, 11, 11, 11, 10, 9, 9, 9, 8, 8, 8, 8, 9, 8, 7, 7, 7, 7, 6, 6, 6, 6, 6, 7, 6, 7, 6, 6, 7, 6, 5, 7, 6, 6, 5, 5, 5, 5, 5, 6, 6, 5, 4};
  for (int i = 0; i < 74; i++)
    bound[i] = vals[i];
}
void strategy0(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[38] = {72, 48, 46, 49, 52, 69, 66, 56, 57, 63, 64, 65, 62, 51, 25, 23, 29, 33, 43, 44, 21, 9, 16, 17, 19, 61, 27, 38, 34, 30, 31, 28, 13, 12, 20, 15, 11, 10};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x99bb52284b7e421f, 0x56b43e2cbb6a4e15, 0x102e4fae1fa9c46a, 0x36aac7f1a591, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 38; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x6bb91e43b2e52683, 0x97e6be1533f6f0dd, 0x5ae9d39331fa84f, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0xe44bff2c24f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x1134a7b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x973, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x37c15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14bf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1aa9938617, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x341a87dd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5855ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x82b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x133, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(61, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 307, 0);
    e[61] = ec - (1 ^ bc);
    counter[61] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x8a367e0e87805fa7, 0x502768f0056, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x6588f15573277, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0758b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x26519, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x53, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x829e284f0d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa9bca189d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x123a0de9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24bd97, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x60f7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(51, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 241, 0);
    e[51] = ec - (1 ^ bc);
    counter[51] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc94b14fbee538d11, 0x41fa934ae, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(65, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd2340baa23860d93, 0x330767d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 331, 0);
    e[65] = ec - (1 ^ bc);
    counter[65] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(64, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x98bdfbbe4a7970f, 0x2935a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 317, 0);
    e[64] = ec - (1 ^ bc);
    counter[64] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(63, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x472fe273ec488287, 0x21b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 313, 0);
    e[63] = ec - (1 ^ bc);
    counter[63] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(57, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf264e8c9e434042b, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 277, 0);
    e[57] = ec - (1 ^ bc);
    counter[57] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d6cecae6645325, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(66, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x165a571dedf95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 337, 0);
    e[66] = ec - (1 ^ bc);
    counter[66] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(69, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1035e99a6b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 353, 0);
    e[69] = ec - (1 ^ bc);
    counter[69] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(52, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10889480f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 251, 0);
    e[52] = ec - (1 ^ bc);
    counter[52] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(49, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x122a637, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 233, 0);
    e[49] = ec - (1 ^ bc);
    counter[49] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14da9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x175, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(72, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 373, 0);
    e[72] = ec - (1 ^ bc);
    counter[72] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy1(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[36] = {73, 50, 47, 58, 59, 68, 53, 67, 60, 71, 54, 70, 24, 36, 37, 45, 35, 55, 22, 26, 42, 41, 32, 40, 39, 14, 18, 8, 7, 6, 4, 5, 3, 0, 1, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xd695aeee6f7e9001, 0x5a3ad670f64e515c, 0x64578dd369cbd6b4, 0x92d6c0fed4d86b55, 0x7711, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 36; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[7];
  proj pts_d[7];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9983e53022b1e2cf, 0x30108b3320bfbe10, 0xd6, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x870c758917e1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0xa4729, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  {u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[6] = R_r;
  pts_d[6] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x250f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbf021050c03, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x15fc8dd969, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d7807d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x271697, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5d85, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(55, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 269, 0);
    e[55] = ec - (1 ^ bc);
    counter[55] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9fcc9afd3cfe2987, 0x733e106, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x307d29b88d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3ad4851f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5a2ec9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8da3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(70, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 359, 0);
    e[70] = ec - (1 ^ bc);
    counter[70] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x68c27b3c56dcf381, 0x702cd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(71, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf5d27de4f5c6020f, 0x4e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 367, 0);
    e[71] = ec - (1 ^ bc);
    counter[71] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(60, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x45dce55827485223, 0x4, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 293, 0);
    e[60] = ec - (1 ^ bc);
    counter[60] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(67, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x326ffec55b144d9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 347, 0);
    e[67] = ec - (1 ^ bc);
    counter[67] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(53, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x323dc10456bd9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 257, 0);
    e[53] = ec - (1 ^ bc);
    counter[53] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(68, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24da68e80ad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 349, 0);
    e[68] = ec - (1 ^ bc);
    counter[68] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x21564e9d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(58, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1e5f06f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 281, 0);
    e[58] = ec - (1 ^ bc);
    counter[58] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x22405, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(50, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 239, 0);
    e[50] = ec - (1 ^ bc);
    counter[50] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(73, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 587, 0);
    e[73] = ec - (1 ^ bc);
    counter[73] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy2(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[38] = {72, 48, 46, 49, 52, 69, 66, 56, 57, 63, 64, 65, 62, 51, 25, 23, 29, 33, 43, 44, 21, 9, 16, 17, 19, 61, 27, 38, 34, 30, 31, 28, 13, 12, 20, 15, 11, 10};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x99bb52284b7e421f, 0x56b43e2cbb6a4e15, 0x102e4fae1fa9c46a, 0x36aac7f1a591, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 38; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x6bb91e43b2e52683, 0x97e6be1533f6f0dd, 0x5ae9d39331fa84f, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0xe44bff2c24f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x1134a7b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x973, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x37c15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14bf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1aa9938617, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x341a87dd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5855ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x82b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x133, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(61, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 307, 0);
    e[61] = ec - (1 ^ bc);
    counter[61] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x8a367e0e87805fa7, 0x502768f0056, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x6588f15573277, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0758b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x26519, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x53, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x829e284f0d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa9bca189d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x123a0de9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24bd97, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x60f7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(51, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 241, 0);
    e[51] = ec - (1 ^ bc);
    counter[51] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc94b14fbee538d11, 0x41fa934ae, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(65, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd2340baa23860d93, 0x330767d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 331, 0);
    e[65] = ec - (1 ^ bc);
    counter[65] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(64, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x98bdfbbe4a7970f, 0x2935a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 317, 0);
    e[64] = ec - (1 ^ bc);
    counter[64] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(63, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x472fe273ec488287, 0x21b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 313, 0);
    e[63] = ec - (1 ^ bc);
    counter[63] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(57, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf264e8c9e434042b, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 277, 0);
    e[57] = ec - (1 ^ bc);
    counter[57] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d6cecae6645325, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(66, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x165a571dedf95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 337, 0);
    e[66] = ec - (1 ^ bc);
    counter[66] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(69, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1035e99a6b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 353, 0);
    e[69] = ec - (1 ^ bc);
    counter[69] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(52, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10889480f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 251, 0);
    e[52] = ec - (1 ^ bc);
    counter[52] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(49, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x122a637, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 233, 0);
    e[49] = ec - (1 ^ bc);
    counter[49] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14da9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x175, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(72, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 373, 0);
    e[72] = ec - (1 ^ bc);
    counter[72] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy3(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[36] = {73, 50, 47, 58, 59, 68, 53, 67, 60, 71, 54, 70, 24, 36, 37, 45, 35, 55, 22, 26, 42, 41, 32, 40, 39, 14, 18, 8, 7, 6, 4, 5, 3, 0, 1, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xd695aeee6f7e9001, 0x5a3ad670f64e515c, 0x64578dd369cbd6b4, 0x92d6c0fed4d86b55, 0x7711, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 36; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[7];
  proj pts_d[7];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9983e53022b1e2cf, 0x30108b3320bfbe10, 0xd6, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x870c758917e1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0xa4729, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  {u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[6] = R_r;
  pts_d[6] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x250f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbf021050c03, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x15fc8dd969, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d7807d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x271697, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5d85, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(55, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 269, 0);
    e[55] = ec - (1 ^ bc);
    counter[55] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9fcc9afd3cfe2987, 0x733e106, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x307d29b88d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3ad4851f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5a2ec9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8da3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(70, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 359, 0);
    e[70] = ec - (1 ^ bc);
    counter[70] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x68c27b3c56dcf381, 0x702cd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(71, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf5d27de4f5c6020f, 0x4e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 367, 0);
    e[71] = ec - (1 ^ bc);
    counter[71] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(60, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x45dce55827485223, 0x4, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 293, 0);
    e[60] = ec - (1 ^ bc);
    counter[60] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(67, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x326ffec55b144d9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 347, 0);
    e[67] = ec - (1 ^ bc);
    counter[67] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(53, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x323dc10456bd9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 257, 0);
    e[53] = ec - (1 ^ bc);
    counter[53] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(68, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24da68e80ad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 349, 0);
    e[68] = ec - (1 ^ bc);
    counter[68] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x21564e9d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(58, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1e5f06f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 281, 0);
    e[58] = ec - (1 ^ bc);
    counter[58] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x22405, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(50, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 239, 0);
    e[50] = ec - (1 ^ bc);
    counter[50] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(73, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 587, 0);
    e[73] = ec - (1 ^ bc);
    counter[73] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy4(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[38] = {72, 48, 46, 49, 52, 69, 66, 56, 57, 63, 64, 65, 62, 51, 25, 23, 29, 33, 43, 44, 21, 9, 16, 17, 19, 61, 27, 38, 34, 30, 31, 28, 13, 12, 20, 15, 11, 10};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x99bb52284b7e421f, 0x56b43e2cbb6a4e15, 0x102e4fae1fa9c46a, 0x36aac7f1a591, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 38; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x6bb91e43b2e52683, 0x97e6be1533f6f0dd, 0x5ae9d39331fa84f, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0xe44bff2c24f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x1134a7b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x973, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x37c15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14bf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1aa9938617, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x341a87dd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5855ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x82b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x133, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(61, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 307, 0);
    e[61] = ec - (1 ^ bc);
    counter[61] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x8a367e0e87805fa7, 0x502768f0056, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x6588f15573277, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0758b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x26519, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x53, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x829e284f0d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa9bca189d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x123a0de9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24bd97, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x60f7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(51, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 241, 0);
    e[51] = ec - (1 ^ bc);
    counter[51] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc94b14fbee538d11, 0x41fa934ae, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(65, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd2340baa23860d93, 0x330767d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 331, 0);
    e[65] = ec - (1 ^ bc);
    counter[65] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(64, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x98bdfbbe4a7970f, 0x2935a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 317, 0);
    e[64] = ec - (1 ^ bc);
    counter[64] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(63, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x472fe273ec488287, 0x21b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 313, 0);
    e[63] = ec - (1 ^ bc);
    counter[63] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(57, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf264e8c9e434042b, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 277, 0);
    e[57] = ec - (1 ^ bc);
    counter[57] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d6cecae6645325, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(66, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x165a571dedf95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 337, 0);
    e[66] = ec - (1 ^ bc);
    counter[66] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(69, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1035e99a6b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 353, 0);
    e[69] = ec - (1 ^ bc);
    counter[69] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(52, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10889480f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 251, 0);
    e[52] = ec - (1 ^ bc);
    counter[52] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(49, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x122a637, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 233, 0);
    e[49] = ec - (1 ^ bc);
    counter[49] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14da9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x175, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(72, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 373, 0);
    e[72] = ec - (1 ^ bc);
    counter[72] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy5(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[36] = {73, 50, 47, 58, 59, 68, 53, 67, 60, 71, 54, 70, 24, 36, 37, 45, 35, 55, 22, 26, 42, 41, 32, 40, 39, 14, 18, 8, 7, 6, 4, 5, 3, 0, 1, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xd695aeee6f7e9001, 0x5a3ad670f64e515c, 0x64578dd369cbd6b4, 0x92d6c0fed4d86b55, 0x7711, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 36; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[7];
  proj pts_d[7];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9983e53022b1e2cf, 0x30108b3320bfbe10, 0xd6, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x870c758917e1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0xa4729, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  {u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[6] = R_r;
  pts_d[6] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x250f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbf021050c03, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x15fc8dd969, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d7807d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x271697, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5d85, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(55, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 269, 0);
    e[55] = ec - (1 ^ bc);
    counter[55] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9fcc9afd3cfe2987, 0x733e106, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x307d29b88d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3ad4851f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5a2ec9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8da3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(70, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 359, 0);
    e[70] = ec - (1 ^ bc);
    counter[70] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x68c27b3c56dcf381, 0x702cd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(71, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf5d27de4f5c6020f, 0x4e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 367, 0);
    e[71] = ec - (1 ^ bc);
    counter[71] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(60, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x45dce55827485223, 0x4, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 293, 0);
    e[60] = ec - (1 ^ bc);
    counter[60] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(67, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x326ffec55b144d9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 347, 0);
    e[67] = ec - (1 ^ bc);
    counter[67] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(53, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x323dc10456bd9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 257, 0);
    e[53] = ec - (1 ^ bc);
    counter[53] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(68, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24da68e80ad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 349, 0);
    e[68] = ec - (1 ^ bc);
    counter[68] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x21564e9d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(58, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1e5f06f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 281, 0);
    e[58] = ec - (1 ^ bc);
    counter[58] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x22405, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(50, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 239, 0);
    e[50] = ec - (1 ^ bc);
    counter[50] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(73, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 587, 0);
    e[73] = ec - (1 ^ bc);
    counter[73] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy6(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[38] = {72, 48, 46, 49, 52, 69, 66, 56, 57, 63, 64, 65, 62, 51, 25, 23, 29, 33, 43, 44, 21, 9, 16, 17, 19, 61, 27, 38, 34, 30, 31, 28, 13, 12, 20, 15, 11, 10};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x99bb52284b7e421f, 0x56b43e2cbb6a4e15, 0x102e4fae1fa9c46a, 0x36aac7f1a591, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 38; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x6bb91e43b2e52683, 0x97e6be1533f6f0dd, 0x5ae9d39331fa84f, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0xe44bff2c24f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x1134a7b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x973, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x37c15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14bf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1aa9938617, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x341a87dd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5855ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x82b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x133, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(61, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 307, 0);
    e[61] = ec - (1 ^ bc);
    counter[61] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x8a367e0e87805fa7, 0x502768f0056, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x6588f15573277, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0758b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x26519, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa0d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x53, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x829e284f0d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa9bca189d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x123a0de9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24bd97, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x60f7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(51, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 241, 0);
    e[51] = ec - (1 ^ bc);
    counter[51] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc94b14fbee538d11, 0x41fa934ae, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(65, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd2340baa23860d93, 0x330767d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 331, 0);
    e[65] = ec - (1 ^ bc);
    counter[65] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(64, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x98bdfbbe4a7970f, 0x2935a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 317, 0);
    e[64] = ec - (1 ^ bc);
    counter[64] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(63, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x472fe273ec488287, 0x21b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 313, 0);
    e[63] = ec - (1 ^ bc);
    counter[63] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(57, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf264e8c9e434042b, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 277, 0);
    e[57] = ec - (1 ^ bc);
    counter[57] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d6cecae6645325, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(66, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x165a571dedf95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 337, 0);
    e[66] = ec - (1 ^ bc);
    counter[66] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(69, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1035e99a6b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 353, 0);
    e[69] = ec - (1 ^ bc);
    counter[69] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(52, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10889480f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 251, 0);
    e[52] = ec - (1 ^ bc);
    counter[52] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(49, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x122a637, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 233, 0);
    e[49] = ec - (1 ^ bc);
    counter[49] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14da9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x175, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(72, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 373, 0);
    e[72] = ec - (1 ^ bc);
    counter[72] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy7(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[36] = {73, 50, 47, 58, 59, 68, 53, 67, 60, 71, 54, 70, 24, 36, 37, 45, 35, 55, 22, 26, 42, 41, 32, 40, 39, 14, 18, 8, 7, 6, 4, 5, 3, 0, 1, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xd695aeee6f7e9001, 0x5a3ad670f64e515c, 0x64578dd369cbd6b4, 0x92d6c0fed4d86b55, 0x7711, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 36; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[7];
  proj pts_d[7];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9983e53022b1e2cf, 0x30108b3320bfbe10, 0xd6, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x870c758917e1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0xa4729, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  {u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[6] = R_r;
  pts_d[6] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x250f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbf021050c03, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x15fc8dd969, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d7807d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x271697, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5d85, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(55, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 269, 0);
    e[55] = ec - (1 ^ bc);
    counter[55] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9fcc9afd3cfe2987, 0x733e106, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x307d29b88d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3ad4851f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5a2ec9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8da3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(70, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 359, 0);
    e[70] = ec - (1 ^ bc);
    counter[70] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x68c27b3c56dcf381, 0x702cd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(71, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf5d27de4f5c6020f, 0x4e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 367, 0);
    e[71] = ec - (1 ^ bc);
    counter[71] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(60, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x45dce55827485223, 0x4, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 293, 0);
    e[60] = ec - (1 ^ bc);
    counter[60] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(67, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x326ffec55b144d9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 347, 0);
    e[67] = ec - (1 ^ bc);
    counter[67] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(53, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x323dc10456bd9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 257, 0);
    e[53] = ec - (1 ^ bc);
    counter[53] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(68, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24da68e80ad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 349, 0);
    e[68] = ec - (1 ^ bc);
    counter[68] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x21564e9d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(58, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1e5f06f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 281, 0);
    e[58] = ec - (1 ^ bc);
    counter[58] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x22405, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(50, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x24b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 239, 0);
    e[50] = ec - (1 ^ bc);
    counter[50] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(73, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 587, 0);
    e[73] = ec - (1 ^ bc);
    counter[73] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy8(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[41] = {72, 47, 48, 49, 52, 68, 66, 65, 64, 63, 61, 62, 60, 15, 25, 28, 39, 41, 40, 51, 16, 21, 22, 23, 24, 37, 31, 30, 70, 29, 27, 32, 33, 34, 35, 26, 8, 13, 14, 19, 18};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x1c2e0ab667263475, 0x2c8ae5f32365bb4e, 0x7d2f3b33b140f0d2, 0x13f1c4, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 41; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[3];
  proj pts_d[3];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x44a69d958e045809, 0x3454d7414f098684, 0x90ca31988ecae0c9, 0x4093e, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x8ab3b2275ed71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x21a1e80d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x75f1a5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x239b1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe229e6295e5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x17f6e070e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x292c7597, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4bd4a5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb219, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(70, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 359, 0);
    e[70] = ec - (1 ^ bc);
    counter[70] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x910fa7da7ab40687, 0x699f996425f37a5e, 0x175951, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x567a5a373a3a25, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa1980423edbd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf7b671a6fb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x273dda3df, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6790c3f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x129e57, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x396d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(51, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 241, 0);
    e[51] = ec - (1 ^ bc);
    counter[51] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x4a43871917698977, 0x547481aa3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x641a0f1354d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x862af80f3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbfe1ec1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1b2b51, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4387, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x125, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(60, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 293, 0);
    e[60] = ec - (1 ^ bc);
    counter[60] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb064a43dd127d9c1, 0x4584f1b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(61, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2d9a984ceb00213b, 0x39f87, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 307, 0);
    e[61] = ec - (1 ^ bc);
    counter[61] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(63, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9dffad0fc9225a13, 0x2f6, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 313, 0);
    e[63] = ec - (1 ^ bc);
    counter[63] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(64, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x64a320d94950dd8f, 0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 317, 0);
    e[64] = ec - (1 ^ bc);
    counter[64] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(65, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d9d277c31f2e4d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 331, 0);
    e[65] = ec - (1 ^ bc);
    counter[65] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(66, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167efa4a97e3d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 337, 0);
    e[66] = ec - (1 ^ bc);
    counter[66] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(68, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x108059b4261, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 349, 0);
    e[68] = ec - (1 ^ bc);
    counter[68] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(52, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10d480353, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 251, 0);
    e[52] = ec - (1 ^ bc);
    counter[52] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(49, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x127dcdb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 233, 0);
    e[49] = ec - (1 ^ bc);
    counter[49] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14abf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x175, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(72, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 373, 0);
    e[72] = ec - (1 ^ bc);
    counter[72] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy9(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[32] = {71, 50, 44, 45, 46, 67, 69, 56, 59, 58, 57, 53, 54, 55, 38, 36, 43, 42, 20, 11, 12, 17, 9, 7, 10, 4, 5, 6, 3, 0, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x17da57f28baec221, 0xc2c7f7e274021db6, 0xcc1b3d97c1d02bf4, 0x8106a8525e26112, 0x2ec57c635d00c, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 32; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[8];
  proj pts_d[8];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x5d265acb96ea3bdf, 0x2005774e79b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x43268b5467, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x8e6367, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x670d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  {u512 coef = { .c = {0x13, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[6] = R_r;
  pts_d[6] = R_d;
  {u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[7] = R_r;
  pts_d[7] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 8, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[7];
  R_d = pts_d[7];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 8, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[7];
  R_d = pts_d[7];
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2200d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xca7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5911f727, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x73befb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb5c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(55, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 269, 0);
    e[55] = ec - (1 ^ bc);
    counter[55] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc7e5dd4dabe3b069, 0x1f2b48542, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(53, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x81469f3e0f9c4769, 0x1f0c3c1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 257, 0);
    e[53] = ec - (1 ^ bc);
    counter[53] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(57, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x93699cc33a47ba05, 0x1cb1a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 277, 0);
    e[57] = ec - (1 ^ bc);
    counter[57] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(58, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x421e709d646bc1cd, 0x1a2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 281, 0);
    e[58] = ec - (1 ^ bc);
    counter[58] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x7a5a912206afdf37, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x165696442266f59, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(69, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x103330c8418f9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 353, 0);
    e[69] = ec - (1 ^ bc);
    counter[69] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(67, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbf3994ab3b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 347, 0);
    e[67] = ec - (1 ^ bc);
    counter[67] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xdb85d525, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10a5727, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x156a1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(50, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 239, 0);
    e[50] = ec - (1 ^ bc);
    counter[50] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(71, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 367, 0);
    e[71] = ec - (1 ^ bc);
    counter[71] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy10(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[33] = {71, 52, 41, 50, 46, 40, 51, 42, 57, 56, 54, 53, 55, 49, 15, 16, 22, 23, 32, 36, 37, 47, 14, 24, 25, 26, 39, 38, 28, 8, 13, 18, 17};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x174f1f0e7ddbf13f, 0xeddba47643e92ae2, 0x38c19243590f5459, 0x36b026d2ffa45d11, 0x1f4f3, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 33; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[3];
  proj pts_d[3];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xc458f3fc25d4fe7, 0x465a11944d763f9a, 0x33b2d21d, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x1792ce9e9bd29, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa6dc35, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x259a3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xccd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x22e21e831ed, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x31e3912df, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x775c45d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x128a9b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2eff, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xf0cc0e1acbf2720f, 0x88000b8e4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x952d54c5322f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xea4a560505, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1af7fb2af, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x472cd0f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xccba7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x35b3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(49, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 233, 0);
    e[49] = ec - (1 ^ bc);
    counter[49] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(55, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1b8ac04a5481608b, 0x816d7c3f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 269, 0);
    e[55] = ec - (1 ^ bc);
    counter[55] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(53, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xaf6c1ea1a8abd58b, 0x80ec8f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 257, 0);
    e[53] = ec - (1 ^ bc);
    counter[53] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1ce5280674795a5d, 0x7d7e, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8bea2c8bd4f9d5d3, 0x76, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(57, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6d8f2b98feeba547, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 277, 0);
    e[57] = ec - (1 ^ bc);
    counter[57] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x915276d833a007, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(51, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9a5df8663077, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 241, 0);
    e[51] = ec - (1 ^ bc);
    counter[51] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xda54d1e3fb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xfaa3f465, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(50, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10c77eb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 239, 0);
    e[50] = ec - (1 ^ bc);
    counter[50] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167d5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(52, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 251, 0);
    e[52] = ec - (1 ^ bc);
    counter[52] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(71, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 367, 0);
    e[71] = ec - (1 ^ bc);
    counter[71] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy11(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[33] = {70, 43, 44, 45, 58, 63, 59, 62, 60, 64, 27, 20, 33, 34, 48, 29, 30, 35, 31, 21, 11, 12, 19, 9, 7, 10, 4, 5, 6, 3, 0, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x11232b6db6c50fe9, 0x925b5a8492a6d5df, 0x178dff0cab2e15e8, 0xa32dcde1ffe9b957, 0xe1c73f6f5dfb, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 33; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[8];
  proj pts_d[8];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x7e9f0032e72b7fb, 0x14650c9d75a8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x1314653f95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0xa2fea1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x670d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  {u512 coef = { .c = {0x13, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[6] = R_r;
  pts_d[6] = R_d;
  {u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[7] = R_r;
  pts_d[7] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x15, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 8, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[7];
  R_d = pts_d[7];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 8, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 7; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[7];
  R_d = pts_d[7];
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 7, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 6; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[6];
  R_d = pts_d[6];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x23b99, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd4b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x53, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x23a70bad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3a2251, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x719b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x2000e64dd351611f, 0x16d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x183e1b23, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29a6d7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x86f9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x13d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(64, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 317, 0);
    e[64] = ec - (1 ^ bc);
    counter[64] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(60, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3f045f25d5e8aff3, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 293, 0);
    e[60] = ec - (1 ^ bc);
    counter[60] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10699697c291525, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xed8bae1ee6bf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(63, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc249593fb7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 313, 0);
    e[63] = ec - (1 ^ bc);
    counter[63] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(58, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb100514f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 281, 0);
    e[58] = ec - (1 ^ bc);
    counter[58] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd6c015, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11443, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(70, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 359, 0);
    e[70] = ec - (1 ^ bc);
    counter[70] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy12(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[53] = {62, 59, 56, 54, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x6f50134414bab42d, 0xac2f997ad5a5273d, 0x3b7b3e8a423b, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 53; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[6];
  proj pts_d[6];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x22a4d6ba33d76f6d, 0x92bbb63753cf2480, 0x278733b6c8cfd4, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x2b71afe09dc0f5d, 0x3912, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x3ae14983f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0xbac79, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0x1067, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  ec = lookup(0, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 3, 0);
    e[0] = ec - (1 ^ bc);
    counter[0] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x13, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x81ef, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x47b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x25, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16fa4227, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x88cbf5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2e91b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe0f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  {u512 coef = { .c = {0x6ba61863ec95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x20691a3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x74dc5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x199d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x53, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x135a43aa69d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x33132bfbd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8175079, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x141c1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x301d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x2f549fedddb4a3df, 0xf9d49157042f69d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x51a57dfe9b04d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9f8daa012ef, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x12a24be9b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x22519505, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3af6b1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x63f7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xb1f422d83e26e49d, 0x7f5f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x301b66295d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x472ff171, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x65cf4b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8fff, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x85739837ad25e1f9, 0xa5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd4ee9221ba1dc73f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(45, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x102580c4ae43c65, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 211, 0);
    e[45] = ec - (1 ^ bc);
    counter[45] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(46, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x12892ff30173b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 223, 0);
    e[46] = ec - (1 ^ bc);
    counter[46] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(47, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14e766917c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 227, 0);
    e[47] = ec - (1 ^ bc);
    counter[47] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(48, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x175e5a115, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 229, 0);
    e[48] = ec - (1 ^ bc);
    counter[48] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(54, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16bf203, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 263, 0);
    e[54] = ec - (1 ^ bc);
    counter[54] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(56, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x157cd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 271, 0);
    e[56] = ec - (1 ^ bc);
    counter[56] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(59, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x137, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 283, 0);
    e[59] = ec - (1 ^ bc);
    counter[59] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(62, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 311, 0);
    e[62] = ec - (1 ^ bc);
    counter[62] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy13(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[44] = {44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xa258a92f054ef639, 0x486108fa0a41324b, 0x1b1423ec6e7e0375, 0x946c7af8498e, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 44; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[6];
  proj pts_d[6];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xf5f7833ad311b40d, 0xaf16f153f37ca169, 0x3bb, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0xe5b65ed6608b952d, 0x27, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x9af6835, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x5fe9f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[5] = R_r;
  pts_d[5] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 6, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 5; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[5];
  R_d = pts_d[5];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x50c5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x383, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4302d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a269, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9bb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x35, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  {u512 coef = { .c = {0x891be12f7f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14339c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x54c7d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x49, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1bc4d61d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x55a60cb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf65c3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x28a3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x67, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x967928ffeb7ba411, 0x452e6, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x210d004619ff7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4d9fb57cb73, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xafdb17c23, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1627b25d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2b4b9f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x50e7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x99944c901afd6d97, 0x754, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf3ef021e44a7eec3, 0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x12c5c90b2df79b61, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1cc6f3cdb03cb7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2a9562da8b73, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(39, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3ce6cf2a41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 179, 0);
    e[39] = ec - (1 ^ bc);
    counter[39] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(40, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x562316dd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 181, 0);
    e[40] = ec - (1 ^ bc);
    counter[40] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(41, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x737363, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 191, 0);
    e[41] = ec - (1 ^ bc);
    counter[41] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(42, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9923, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 193, 0);
    e[42] = ec - (1 ^ bc);
    counter[42] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(44, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 199, 0);
    e[44] = ec - (1 ^ bc);
    counter[44] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy14(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[39] = {43, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x7bb0e208adcf87df, 0x5376eb6d929de75a, 0x23534b7f507f5f34, 0xaed642e120b009f7, 0x201552, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 39; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[5];
  proj pts_d[5];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x153e66f494a07671, 0x109eb3c9574c606, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x193690a930fc5eb5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x37ed0ed, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x1d05, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3e9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x17, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1edb11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xfecf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  {u512 coef = { .c = {0x2f2f024fc1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2e91b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe0f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb448a1ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x28a097d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8e795, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1cdb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x59, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x2a7041c57adaf09b, 0x1bb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x195682d1ec3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x40390ec07, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9f9f361, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x17de63, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x380f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x7f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6208ac78b6ada409, 0x3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x652484426b4a781, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xba46efe6fcda3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1400beb36f57, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x21e9871f41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x374bddf5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(36, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x56d887, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 163, 0);
    e[36] = ec - (1 ^ bc);
    counter[36] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(37, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8521, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 167, 0);
    e[37] = ec - (1 ^ bc);
    counter[37] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(38, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 173, 0);
    e[38] = ec - (1 ^ bc);
    counter[38] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(43, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 197, 0);
    e[43] = ec - (1 ^ bc);
    counter[43] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy15(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[35] = {35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x294c5258373d8b6b, 0xda6c866d9ecc3c2, 0x2f7c1c1b2159498d, 0x40c4c063451221a3, 0x6ee16d3e60a34, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 35; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[5];
  proj pts_d[5];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x429ee5d8ff0f1391, 0x2ad2750ab1bb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x2d4db2152a1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x37ed0ed, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x1d05, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3e9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x17, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1edb11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xfecf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf6c26d62f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4a7e5153, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14339c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x54c7d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x49, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xbf4aef85bc989e8d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb9b457e25b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x23cc674d9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x66f8881, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x10fc21, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2b0d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1c1464ebb4582a1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3f9d36312bd31, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x803ae226a4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xfa963ed45, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d43ffdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x35e637, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5c9b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(35, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 157, 0);
    e[35] = ec - (1 ^ bc);
    counter[35] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy16(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[34] = {34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x53ce8019e0be809f, 0x5f48e713a6340e13, 0x1f1d3ca373c21b81, 0xb8a9fce15c1ea114, 0x44003fff414420b, 0x0, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 34; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[5];
  proj pts_d[5];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x1bb7217efc4d1fed, 0x13e931876b19, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x1aaf84f3eb3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x14cf47, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x1d05, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3e9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x17, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb7b3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5ed, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9edf5ef99, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x361592b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1053cbb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x46d81, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1295, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x47, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x825f18a4856ce7fb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x891be12f7f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1bc4d61d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x55a60cb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf65c3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x28a3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x67, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x137eab295955ab1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2dc9340c900d5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x67ba3b038a5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(29, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd116a34db, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 127, 0);
    e[29] = ec - (1 ^ bc);
    counter[29] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x19899ac9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(31, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2fb841, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 137, 0);
    e[31] = ec - (1 ^ bc);
    counter[31] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(32, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x57e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 139, 0);
    e[32] = ec - (1 ^ bc);
    counter[32] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(33, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x97, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 149, 0);
    e[33] = ec - (1 ^ bc);
    counter[33] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(34, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 151, 0);
    e[34] = ec - (1 ^ bc);
    counter[34] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy17(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[29] = {30, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x6404fd2f19c7c8a9, 0xbf258a7933fb1c71, 0xacb5ecf83c46b4a5, 0x8203d4faf4c975a1, 0xc1e0549327b92556, 0x35d812c5, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 29; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[5];
  proj pts_d[5];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x63b2cfff0b9bdc97, 0x1d3437, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x3ae14983f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0xbac79, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0x1067, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x13, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x81ef, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x47b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x25, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16fa4227, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x88cbf5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2e91b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xe0f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x9e730a034257, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb448a1ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x28a097d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8e795, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1cdb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x59, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a22cf81db7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x423ee2deb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xa4a63dd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(26, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x189ed7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 107, 0);
    e[26] = ec - (1 ^ bc);
    counter[26] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x39d3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(28, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x83, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 113, 0);
    e[28] = ec - (1 ^ bc);
    counter[28] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy18(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[27] = {30, 27, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xf7a1ff969ee245f3, 0xf2132a7a15185f7e, 0x346f3046df76104a, 0xaafc28c76706caf8, 0xde3a823525867cce, 0x9ef143ea22b, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 27; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[5];
  proj pts_d[5];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xd382c6a238919641, 0x25b7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x23b6d0437, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x5fe9f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x50c5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x383, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf71a62b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x606e33, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x23e19, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xc37, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x60ce002af077, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a29a93, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x63f71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1687, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x12a940cdacd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x35ad4ff95, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8da9bb5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x167111, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x37c7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(27, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x83, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 109, 0);
    e[27] = ec - (1 ^ bc);
    counter[27] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(30, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 131, 0);
    e[30] = ec - (1 ^ bc);
    counter[30] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy19(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[25] = {25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x4cd70a381eeb94e5, 0x4b063f6ea27682e6, 0xa5cdc11a1246c444, 0x16c68a238be31a34, 0x5174a260105b6b63, 0x22a163231877cd8, 0x0, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 25; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[5];
  proj pts_d[5];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0xe5b65ed6608b952d, 0x27, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x9af6835, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x5fe9f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  {u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[4] = R_r;
  pts_d[4] = R_d;
  ec = lookup(1, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 5, 0);
    e[1] = ec - (1 ^ bc);
    counter[1] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 5, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 4; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[4];
  R_d = pts_d[4];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x50c5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x383, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4302d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a269, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9bb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x35, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x891be12f7f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14339c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x54c7d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x49, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1bc4d61d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x55a60cb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf65c3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(23, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x28a3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 97, 0);
    e[23] = ec - (1 ^ bc);
    counter[23] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(24, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x67, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 101, 0);
    e[24] = ec - (1 ^ bc);
    counter[24] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(25, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 103, 0);
    e[25] = ec - (1 ^ bc);
    counter[25] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy20(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[21] = {22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xd899afc11b0ad12b, 0xa5566d90e30d5bb2, 0xef323b14b4b232ed, 0xdd1237dd720f3cdd, 0xe1aab6eb190c227b, 0xc4c80f907bab11b8, 0xa6a1, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 21; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x29755e17f3a4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x9af6835, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x5fe9f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x97f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x50c5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x383, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4302d1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a269, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x9bb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x35, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb3e338d00fd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2f2f024fc1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb448a1ab, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x28a097d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8e795, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1cdb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(21, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x59, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 83, 0);
    e[21] = ec - (1 ^ bc);
    counter[21] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(22, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 89, 0);
    e[22] = ec - (1 ^ bc);
    counter[22] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy21(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[19] = {20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x1ab279275121a3c9, 0xe4eb93c7b27501b0, 0x1e6ece7a12038f61, 0x1cb202ea3db15805, 0xb90c31dbc1270c24, 0x38d91e20814861d7, 0x12c83de9, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 19; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x4c25ffc1881, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x5aa381f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x97f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2ec801, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143ad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x7e5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16fcfb189d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x63bed507, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a29a93, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x63f71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1687, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy22(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[19] = {20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x1ab279275121a3c9, 0xe4eb93c7b27501b0, 0x1e6ece7a12038f61, 0x1cb202ea3db15805, 0xb90c31dbc1270c24, 0x38d91e20814861d7, 0x12c83de9, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 19; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x4c25ffc1881, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x5aa381f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x97f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2ec801, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143ad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x7e5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x16fcfb189d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x63bed507, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1a29a93, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x63f71, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1687, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(20, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 79, 0);
    e[20] = ec - (1 ^ bc);
    counter[20] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy23(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[18] = {19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x3d13632209618b07, 0xa4b29aa0121b8558, 0x6431b7ab8f193f35, 0xdaeee64909ba2994, 0x1ac362d09b0cbf24, 0x8b004c07e5563192, 0x5cbcb1af8, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 18; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x2d4db2152a1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x1edb11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x3181, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x97f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xdd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x11, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xfecf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x6e3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x2b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xf6c26d62f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x4a7e5153, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x14339c9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(16, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x54c7d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 61, 0);
    e[16] = ec - (1 ^ bc);
    counter[16] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x49, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy24(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[17] = {19, 18, 17, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0x8d9e9f1c3c3e20ab, 0x3e8ed824508ec606, 0xdfd8c3e119040fc8, 0x2aecdf67515be85b, 0x608e8bb4f2098bc8, 0x1f121de1a589cfd0, 0x1618f656d39, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 17; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[4];
  proj pts_d[4];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x1fef6cbf2e7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0x14cf47, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  {u512 coef = { .c = {0x1d05, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[3] = R_r;
  pts_d[3] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x8f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xd, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 4, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 3; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[3];
  R_d = pts_d[3];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x17, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb7b3, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x5ed, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x29, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xbe204be35, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x40b94adb, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x138a0cf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(15, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x54c7d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 59, 0);
    e[15] = ec - (1 ^ bc);
    counter[15] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x49, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(19, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 73, 0);
    e[19] = ec - (1 ^ bc);
    counter[19] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}
void strategy25(proj *A_r, proj *A_d, int8_t *e, int8_t *counter, unsigned int *isog_counter){
  u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};
  int8_t ec = 0;
  uint8_t bc;
  proj P_r, P_d, R_r, R_d;
  u512 k;
  // Prime indices used in strategy:
  int actv_ind[15] = {18, 17, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2};
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_r->x, &fp_0, sizeof(fp))) {
    elligator(&P_r.x, &A_r->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;
  } else {
    fp_enc(&P_r.x, &p_order); // point of full order on E_a with a=0
    P_r.z = fp_1;
  }
  // Choose a random point P with Elligator. When on the base curve, we choose a point of full order
  if(memcmp(&A_d->x, &fp_0, sizeof(fp))) {
    elligator(&P_d.x, &A_d->x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
  } else {
    fp_enc(&P_d.x, &p_order); // point of full order on E_a with a=0
    P_d.z = fp_1;
  }

  // Multiply P by any primes not used in strategy:
  {u512 coef = { .c = {0xa3aee809893f9cf1, 0x7d3e6af7520da040, 0xbe78417df5585f4, 0x2f32973dcd4641b7, 0x7e387544169ab8aa, 0xbdccbb540d934ec8, 0x173c5f876c9805, 0x0}};
  xMUL(&P_r, A_r, &P_r, &coef);
  xMUL(&P_d, A_d, &P_d, &coef);}
  // Multiply P by any primes for which a real isogeny wont be constructed
  for (uint8_t i = 0; i < 15; i++){
    ec = lookup(actv_ind[i], e);  //check in constant-time if normal or dummy isogeny must be computed
    bc = isequal(ec, 0);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
    u512_set(&k, primes[actv_ind[i]]);
    xMUL(&P_d, A_d, &P_d, &k);
    fp_cswap(&P_r.x, &P_d.x, bc);
    fp_cswap(&P_r.z, &P_d.z, bc);
    fp_cswap(&A_r->x, &A_d->x, bc);
    fp_cswap(&A_r->z, &A_d->z, bc);
  }
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  xDBL(&P_r, A_r, &P_r);    // Remove 4-torsion from P
  xDBL(&P_d, A_d, &P_d);
  proj pts_r[3];
  proj pts_d[3];
  pts_r[0] = P_r;
  pts_d[0] = P_d;
  R_r = pts_r[0];
  R_d = pts_d[0];
  {u512 coef = { .c = {0x4dd3355a5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[1] = R_r;
  pts_d[1] = R_d;
  {u512 coef = { .c = {0xbac79, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);
  xMUL(&R_d, A_d, &R_d, &coef);}
  pts_r[2] = R_r;
  pts_d[2] = R_d;
  ec = lookup(2, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb46d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 7, 0);
    e[2] = ec - (1 ^ bc);
    counter[2] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(3, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1067, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 11, 0);
    e[3] = ec - (1 ^ bc);
    counter[3] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(4, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x143, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 13, 0);
    e[4] = ec - (1 ^ bc);
    counter[4] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(5, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x13, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 3, &R_r, 17, 0);
    e[5] = ec - (1 ^ bc);
    counter[5] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 2; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[2];
  R_d = pts_d[2];
  ec = lookup(6, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 19, 0);
    e[6] = ec - (1 ^ bc);
    counter[6] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(7, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x81ef, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 23, 0);
    e[7] = ec - (1 ^ bc);
    counter[7] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(8, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x47b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 29, 0);
    e[8] = ec - (1 ^ bc);
    counter[8] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(9, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x25, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 2, &R_r, 31, 0);
    e[9] = ec - (1 ^ bc);
    counter[9] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 1; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[1];
  R_d = pts_d[1];
  ec = lookup(10, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 37, 0);
    e[10] = ec - (1 ^ bc);
    counter[10] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(11, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1e5ee91d, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 41, 0);
    e[11] = ec - (1 ^ bc);
    counter[11] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(12, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0xb4cfd7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 43, 0);
    e[12] = ec - (1 ^ bc);
    counter[12] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(13, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x3d8d9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 47, 0);
    e[13] = ec - (1 ^ bc);
    counter[13] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(14, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x1295, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 53, 0);
    e[14] = ec - (1 ^ bc);
    counter[14] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(17, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
{u512 coef = { .c = {0x47, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}};
  xMUL(&R_r, A_r, &R_r, &coef);}
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
    xISOG(A_r, pts_r, 1, &R_r, 67, 0);
    e[17] = ec - (1 ^ bc);
    counter[17] -= 1;
    (*isog_counter)++;
    for (int j = 0; j <= 0; j++){
       fp_cswap(&pts_r[j].x, &pts_d[j].x, bc);
       fp_cswap(&pts_r[j].z, &pts_d[j].z, bc);
    };
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  R_r = pts_r[0];
  R_d = pts_d[0];
  ec = lookup(18, e);
  bc = isequal(ec, 0);
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);
  if (memcmp(&R_r.z, &fp_0, sizeof(fp))){
    lastxISOG(A_r, &R_r, 71, 0);
    e[18] = ec - (1 ^ bc);
    counter[18] -= 1;
    (*isog_counter)++;
  }
  fp_cswap(&A_r->x, &A_d->x, bc);
  fp_cswap(&A_r->z, &A_d->z, bc);
  fp_cswap(&R_r.x, &R_d.x, bc);
  fp_cswap(&R_r.z, &R_d.z, bc);

  // Affinize the curve coefficients
  fp_inv(&A_r->z);
  fp_mul2(&A_r->x, &A_r->z);
  A_r->z = fp_1;
  fp_inv(&A_d->z);
  fp_mul2(&A_d->x, &A_d->z);
  A_d->z = fp_1;

}


void action(public_key *out_r, public_key *out_d, public_key const *in_r, public_key const *in_d, private_key const *priv, int8_t const *max_exponent) {
  int8_t e[num_primes] = {0};
  unsigned int isog_counter = 0;
  int8_t counter[num_primes] = {0};

  memcpy(e, priv->e, sizeof(priv->e));      // Copy of the private key
  memcpy(counter, max_exponent, sizeof(counter));  // Counts how many isogenies have been constructed for each prime

  proj A_r = {in_r->A, fp_1 };   // Projectivize the curve coefficient

  proj A_d = {in_d->A, fp_1 };   // Projectivize the curve coefficient
  strategy0( &A_r, &A_d, e, counter, &isog_counter);
  strategy1( &A_r, &A_d, e, counter, &isog_counter);
  strategy2( &A_r, &A_d, e, counter, &isog_counter);
  strategy3( &A_r, &A_d, e, counter, &isog_counter);
  strategy4( &A_r, &A_d, e, counter, &isog_counter);
  strategy5( &A_r, &A_d, e, counter, &isog_counter);
  strategy6( &A_r, &A_d, e, counter, &isog_counter);
  strategy7( &A_r, &A_d, e, counter, &isog_counter);
  strategy8( &A_r, &A_d, e, counter, &isog_counter);
  strategy9( &A_r, &A_d, e, counter, &isog_counter);
  strategy10( &A_r, &A_d, e, counter, &isog_counter);
  strategy11( &A_r, &A_d, e, counter, &isog_counter);
  strategy12( &A_r, &A_d, e, counter, &isog_counter);
  strategy13( &A_r, &A_d, e, counter, &isog_counter);
  strategy14( &A_r, &A_d, e, counter, &isog_counter);
  strategy15( &A_r, &A_d, e, counter, &isog_counter);
  strategy16( &A_r, &A_d, e, counter, &isog_counter);
  strategy17( &A_r, &A_d, e, counter, &isog_counter);
  strategy18( &A_r, &A_d, e, counter, &isog_counter);
  strategy19( &A_r, &A_d, e, counter, &isog_counter);
  strategy20( &A_r, &A_d, e, counter, &isog_counter);
  strategy21( &A_r, &A_d, e, counter, &isog_counter);
  strategy22( &A_r, &A_d, e, counter, &isog_counter);
  strategy23( &A_r, &A_d, e, counter, &isog_counter);
  strategy24( &A_r, &A_d, e, counter, &isog_counter);
  strategy25( &A_r, &A_d, e, counter, &isog_counter);

  int8_t ec = 0;
  uint8_t mask;
  proj P_r, P_d, R_r;
  u512 cof, pr;
  bool finished[num_primes] = {0};
  u512 k[1];
  // Now finish any isogeny constructions which failed above
  while (isog_counter != 830){
    assert(!memcmp(&A_r.z, &fp_1, sizeof(fp)));
    assert(!memcmp(&A_d.z, &fp_1, sizeof(fp)));

    // Choose a random point P with Elligator.
    elligator(&P_r.x, &A_r.x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_r.z = fp_1;

    // Choose a random point P with Elligator.
    elligator(&P_d.x, &A_d.x, true, elligator_index);
    elligator_index = (elligator_index + 1)%9;
    P_d.z = fp_1;
    u512_set(&k[0], 4);  //recompute factor k
    for (uint8_t i = 0; i < num_primes; i++) {
      if(counter[i]==0) {
        u512_mul3_64(&k[0], &k[0], primes[i]);
        finished[i] = true;
      }
    }
    xMUL(&P_r, &A_r, &P_r, &k[0]);
    xMUL(&P_d, &A_d, &P_d, &k[0]);
    for (uint8_t i = 0; i < num_primes; i = i + 1) {
      if(finished[i] == true) {  //depends only on randomness
        continue;
      }
      else {
        cof = u512_1;
        for (uint8_t j = i + 1; j < num_primes; j = j + 1) {
          if (finished[j] == false)  //depends only on randomness
            u512_mul3_64(&cof, &cof, primes[j]);
          }

        ec = lookup(i,e);
        mask = isequal(ec,0);

        fp_cswap(&A_r.x, &A_d.x, mask);
        fp_cswap(&A_r.z, &A_d.z, mask);
        fp_cswap(&P_r.x, &P_d.x, mask);
        fp_cswap(&P_r.z, &P_d.z, mask);

        xMUL(&R_r, &A_r, &P_r, &cof);
        if (memcmp(&R_r.z, &fp_0, sizeof(fp))) {//depends only on randomness
          xISOG(&A_r, &P_r, 1, &R_r, primes[i], 0);
          e[i] = ec - (1 ^ mask);
          counter[i] = counter[i] - 1;
          isog_counter = isog_counter + 1;
        }
        pr = u512_1;
        u512_mul3_64(&pr, &pr, primes[i]);
        xMUL(&P_d, &A_d, &P_d, &pr);

        fp_cswap(&A_r.x, &A_d.x, mask);
        fp_cswap(&A_r.z, &A_d.z, mask);
        fp_cswap(&P_r.x, &P_d.x, mask);
        fp_cswap(&P_r.z, &P_d.z, mask);

        if(counter[i]==0) {   //depends only on randomness
          finished[i] = true;
          u512_mul3_64(&k[0], &k[0], primes[i]);
        }

          }

    }
    fp_inv(&A_r.z);
    fp_mul2(&A_r.x, &A_r.z);
    A_r.z = fp_1;
    fp_inv(&A_d.z);
    fp_mul2(&A_d.x, &A_d.z);
    A_d.z = fp_1;

  }

  out_r->A = A_r.x;
  out_d->A = A_d.x;
}
/* includes public-key validation. */
bool csidh(public_key *out_r, public_key *out_d, public_key const *in_r, public_key const *in_d, private_key const *priv, int8_t const *max_exponent) {
  if (!validate(in_r) || !validate(in_d)) {
    fp_random(&out_r->A);
    fp_random(&out_d->A);
    return false;
  }
  action(out_r, out_d, in_r, in_d, priv, max_exponent);

  return true;
}
