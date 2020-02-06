void main_F()
{
  uint32_t a = 0;
  uint32_t x = 0;
  uint32_t y = 0;

  x += -(0 != a < 2)&3;

  x ^= -(a == 0)& y; y ^= -(a == 0)& x; x ^= -(a == 0)& y;

  if (y != 0)
    fprintf(stderr, "y not zero at end of block
                     starting at line 6\n");
  if (x != 0)
    fprintf(stderr, "x not zero at end of block
                     starting at line 5\n");
  if (a != 0)
    fprintf(stderr, "a not zero at end of block
                     starting at line 4\n");
}
