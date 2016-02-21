
int main() 
{ 
  unsigned  int a[10]; 
  unsigned int b[10];
   __CPROVER_assert(__CPROVER_forall 
                    {unsigned int i; 
                    (i >= 0 && i < 10) ==> a[i] > 0}, 
                    "Assert_Forall"); 
   __CPROVER_assert(__CPROVER_forall 
                    {unsigned int i;(i>=0 && i <10) ==> 
                    __CPROVER_exists 
                    {unsigned int j; 
                    (j>=0 && j<10) ==> a[i] > b[j]}}, 
                    "Assert_Forall_Exists"); 
   return 0; 
} 
