with System.Storage_Elements;
package TLSF is

   package SSE renames System.Storage_Elements;

   type Pool is limited private;

   function Init_Pool (Addr : System.Address;
                       Len  : SSE.Storage_Count)
                       return Pool;

   function Memory_Allocate (Sz   : SSE.Storage_Count;
                             P    : Pool)
                             return System.Address;

   procedure Memory_Free (Addr : System.Address;
                          P    : Pool);

private

   type Pool_Header;
   type Pool is access all Pool_Header;

end TLSF;
