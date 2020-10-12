#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <time.h>

#include "mont.h"
#include "u512.h"

void xDBLADD(proj *R, proj *S, proj const *P, proj const *Q, proj const *PQ, proj const *A24)
{
    fp tmp0, tmp1, tmp2;        //requires precomputation of A24=(A+2C:4C)

    fp_add3(&tmp0, &P->x, &P->z);
    fp_sub3(&tmp1, &P->x, &P->z);
    fp_sq2(&R->x, &tmp0);
    fp_sub3(&tmp2, &Q->x, &Q->z);
    fp_add3(&S->x, &Q->x, &Q->z);
    fp_mul2(&tmp0, &tmp2);
    fp_sq2(&R->z, &tmp1);
    fp_mul2(&tmp1, &S->x);
    fp_sub3(&tmp2, &R->x, &R->z);
    fp_mul2(&R->z, &A24->z);
    fp_mul2(&R->x, &R->z);
    fp_mul3(&S->x, &A24->x, &tmp2);
    fp_sub3(&S->z, &tmp0, &tmp1);
    fp_add2(&R->z, &S->x);
    fp_add3(&S->x, &tmp0, &tmp1);
    fp_mul2(&R->z, &tmp2);
    fp_sq1(&S->z);
    fp_sq1(&S->x);
    fp_mul2(&S->z, &PQ->x);
    fp_mul2(&S->x, &PQ->z);
}

void xDBL(proj *Q, proj const *A, proj const *P)
{
    fp a, b, c;
    fp_add3(&a, &P->x, &P->z);
    fp_sq1(&a);
    fp_sub3(&b, &P->x, &P->z);
    fp_sq1(&b);
    fp_sub3(&c, &a, &b);
    fp_add2(&b, &b); fp_add2(&b, &b); /* multiplication by 4 */
    fp_mul2(&b, &A->z);
    fp_mul3(&Q->x, &a, &b);
    fp_add3(&a, &A->z, &A->z); /* multiplication by 2 */
    fp_add2(&a, &A->x);
    fp_mul2(&a, &c);
    fp_add2(&a, &b);
    fp_mul3(&Q->z, &a, &c);
}

void xADD(proj *S, proj const *P, proj const *Q, proj const *PQ)
{
    fp a, b, c, d;
    fp_add3(&a, &P->x, &P->z);
    fp_sub3(&b, &P->x, &P->z);
    fp_add3(&c, &Q->x, &Q->z);
    fp_sub3(&d, &Q->x, &Q->z);
    fp_mul2(&a, &d);
    fp_mul2(&b, &c);
    fp_add3(&c, &a, &b);
    fp_sub3(&d, &a, &b);
    fp_sq1(&c);
    fp_sq1(&d);
    fp_mul3(&S->x, &PQ->z, &c);
    fp_mul3(&S->z, &PQ->x, &d);
}

/* Montgomery ladder. */
/* P must not be the unique point of order 2. */
/* not constant-time! */
/* factors are independent from the secret -> no constant-time ladder */
void xMUL(proj *Q, proj const *A, proj const *P, u512 const *k)
{
    proj R = *P;
    proj A24;
    const proj Pcopy = *P; /* in case Q = P */

    Q->x = fp_1;
    Q->z = fp_0;

    fp_add3(&A24.x, &A->z, &A->z);    //precomputation of A24=(A+2C:4C)
    fp_add3(&A24.z, &A24.x, &A24.x);
    fp_add2(&A24.x, &A->x);

    unsigned long i = 512;
    while (--i && !u512_bit(k, i));

    do {

        bool bit = u512_bit(k, i);

        if (bit) { proj T = *Q; *Q = R; R = T; } /* not constant-time */
        //fp_cswap(&Q->x, &R.x, bit);
        //fp_cswap(&Q->z, &R.z, bit);

        xDBLADD(Q, &R, Q, &R, &Pcopy, &A24);

        if (bit) { proj T = *Q; *Q = R; R = T; } /* not constant-time */
        //fp_cswap(&Q->x, &R.x, bit);
        //fp_cswap(&Q->z, &R.z, bit);

    } while (i--);
}

//simultaneous square-and-multiply, computes x^exp and y^exp 
void exp_by_squaring_(fp* x, fp* y, uint64_t exp)
{
	fp result1, result2;
	fp_set(&result1, 1);
	fp_set(&result2, 1);

    while (exp)
    {
        if (exp & 1){
          fp_mul2(&result1, x);
          fp_mul2(&result2, y);
        }
	
        fp_sq1(x);
        fp_sq1(y);
        exp >>= 1;
    }

    fp_set(x, 0);
    fp_add2(x, &result1);
    fp_set(y, 0);
    fp_add2(y, &result2);


}


/* computes the isogeny or dummy isogeny with kernel point K of order k  */
/* evaluates the isogeny at the m many points in the array P  */
/* returns the new curve coefficient A and the images of points P for real isogenies */
/* return the old curve coefficient A and the old points P for dummy isogenies */
void xISOG(proj *A, proj *P, uint64_t m, proj *K, uint64_t k, int mask)
{
    // mask = 0 if and only if real isogeny
    assert (k >= 3);
    assert (k % 2 == 1);

    fp tmp0, tmp1, tmp2, Psum, Pdif;
    proj Aed, prod;
    proj Acopy = *A;

    fp_add3(&Aed.z, &A->z, &A->z);  //compute twisted Edwards curve coefficients
    fp_add3(&Aed.x, &A->x, &Aed.z);
    fp_sub3(&Aed.z, &A->x, &Aed.z);
   
    // CONSTANT TIME :
    proj *R = K;            //K for real iso, P for dum iso
    //proj *S = P;
           
    proj Rmults[k/2];       // Rmults[i].x will be ((i+1)*R).x + ((i+1)*R).z, and Rmults[i].z will be ((i+1)*R).x - ((i+1)*R).z
    proj M[3] = {*R};       // For computing kernel points
    xDBL(&M[1], A, R);

       
    fp_add3(&Rmults[0].x, &M[0].x, &M[0].z);
    fp_sub3(&Rmults[0].z, &M[0].x, &M[0].z);

    if (k == 3){
        prod.x = Rmults[0].z;
        prod.z = Rmults[0].x;
    } else {
        fp_add3(&Rmults[1].x, &M[1].x, &M[1].z);
        fp_sub3(&Rmults[1].z, &M[1].x, &M[1].z);

        fp_mul3(&prod.x, &Rmults[0].z, &Rmults[1].z);
        fp_mul3(&prod.z, &Rmults[0].x, &Rmults[1].x);
    }


    for (uint64_t i = 2; i < k / 2; ++i) {      // Compute kernel points, sum and difference of coordinates, and products of all x and z
        xADD(&M[i % 3], &M[(i - 1) % 3], R, &M[(i - 2) % 3]);
        fp_add3(&Rmults[i].x, &M[i % 3].x, &M[i % 3].z);
        fp_sub3(&Rmults[i].z, &M[i % 3].x, &M[i % 3].z);
        fp_mul2(&prod.x, &Rmults[i].z);
        fp_mul2(&prod.z, &Rmults[i].x);
    }



    for (uint64_t i = 0; i < m; ++i){          // Point evaluations
        proj Pcopy = *(P+i);
        fp_add3(&Psum, &(P+i)->x, &(P+i)->z);
        fp_sub3(&Pdif, &(P+i)->x, &(P+i)->z);
        fp_mul3(&tmp0, &Pdif, &Rmults[0].x);
        fp_mul3(&tmp1, &Psum, &Rmults[0].z);
        fp_add3(&(P+i)->x, &tmp0, &tmp1);
        fp_sub3(&(P+i)->z, &tmp0, &tmp1);
        for (uint64_t j = 1; j < k / 2; ++j) {

            fp_mul3(&tmp0, &Pdif, &Rmults[j].x);
            fp_mul3(&tmp1, &Psum, &Rmults[j].z);
            fp_add3(&tmp2, &tmp0, &tmp1);
            fp_sub3(&tmp1, &tmp0, &tmp1);
            fp_mul2(&(P+i)->x, &tmp2);
            fp_mul2(&(P+i)->z, &tmp1);

        }
        fp_sq1(&(P+i)->x);
        fp_sq1(&(P+i)->z);
        fp_mul2(&(P+i)->x, &Pcopy.x);
        fp_mul2(&(P+i)->z, &Pcopy.z);

        fp_cswap(&(P+i)->x, &Pcopy.x, mask);     // Swap back to original value for dummy isogenies
        fp_cswap(&(P+i)->z, &Pcopy.z, mask);

    }

    //compute Aed.x^k, Aed.z^k
    exp_by_squaring_(&Aed.x, &Aed.z, k);

    //compute prod.x^8, prod.z^8
    fp_sq1(&prod.x);
    fp_sq1(&prod.x);
    fp_sq1(&prod.x);
    fp_sq1(&prod.z);
    fp_sq1(&prod.z);
    fp_sq1(&prod.z);

    //compute image curve parameters
    fp_mul2(&Aed.z, &prod.x);
    fp_mul2(&Aed.x, &prod.z);

    //compute Montgomery params
    fp_add3(&A->x, &Aed.x, &Aed.z);
    fp_sub3(&A->z, &Aed.x, &Aed.z);
    fp_add2(&A->x, &A->x);

    // CONSTANT TIME : swap back
    fp_cswap(&A->x, &Acopy.x, mask);
    fp_cswap(&A->z, &Acopy.z, mask);


}

/* computes the last real/dummy isogeny per batch with kernel point K of order k */
/* real isogeny: returns the new curve coefficient A, no point evaluation */
/* dummy isogeny: returns the old curve coefficient A, no point evaluation */
//void lastxISOG(proj *A, proj *P, proj const *K, uint64_t k, int mask)
void lastxISOG(proj *A, proj const *K, uint64_t k, int mask)
{
    // This function is probably equivalent to calling xISOG with m = 0
    assert (k >= 3);
    assert (k % 2 == 1);

    fp tmp0, tmp1;
    proj Aed, prod;
    proj Acopy = *A;

    fp_add3(&Aed.z, &A->z, &A->z);  //compute twisted Edwards curve coefficients
    fp_add3(&Aed.x, &A->x, &Aed.z);
    fp_sub3(&Aed.z, &A->x, &Aed.z);

    fp_sub3(&prod.x, &K->x, &K->z);
    fp_add3(&prod.z, &K->x, &K->z);

    proj M[3] = {*K};
    xDBL(&M[1], A, K);

    for (uint64_t i = 1; i < k / 2; ++i) {

        if (i >= 2)
            xADD(&M[i % 3], &M[(i - 1) % 3], K, &M[(i - 2) % 3]);
        fp_sub3(&tmp1, &M[i % 3].x, &M[i % 3].z);
        fp_add3(&tmp0, &M[i % 3].x, &M[i % 3].z);
        fp_mul2(&prod.x, &tmp1);
        fp_mul2(&prod.z, &tmp0);

    }

    //compute Aed.x^k, Aed.z^k
    exp_by_squaring_(&Aed.x, &Aed.z, k);

    //compute prod.x^8, prod.z^8
    fp_sq1(&prod.x);
    fp_sq1(&prod.x);
    fp_sq1(&prod.x);
    fp_sq1(&prod.z);
    fp_sq1(&prod.z);
    fp_sq1(&prod.z);

    //compute image curve parameters
    fp_mul2(&Aed.z, &prod.x);
    fp_mul2(&Aed.x, &prod.z);

    //compute Montgomery params
    fp_add3(&A->x, &Aed.x, &Aed.z);
    fp_sub3(&A->z, &Aed.x, &Aed.z);
    fp_add2(&A->x, &A->x);

    // CONSTANT TIME : swap back
    fp_cswap(&A->x, &Acopy.x, mask);
    fp_cswap(&A->z, &Acopy.z, mask);

}
