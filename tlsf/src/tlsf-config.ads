private package TLSF.Config
with SPARK_Mode is

   Max_Block_Size_Log2 : constant := 29; -- max Block is about 512Mb
   SL_Index_Count_Log2 : constant := 6;
   Align_Size_Log2     : constant := 3;  -- for 32bit system: 2

   FL_Index_Max        : constant := Max_Block_Size_Log2 - 1;
   Align_Size          : constant := 2 ** Align_Size_Log2;
   SL_Index_Count      : constant := 2 ** SL_Index_Count_Log2;
   FL_Index_Shift      : constant := SL_Index_Count_Log2;
   FL_Index_Count      : constant := FL_Index_Max - FL_Index_Shift + 1;

end TLSF.Config;
