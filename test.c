#include <iostream>

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

using namespace std;

int  main(){
  uint32_t a = 1, b=0;

  cout << isequal(a,b) << '\n';

  return 0;
}
