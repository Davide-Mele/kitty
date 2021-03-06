Truth table data structures
===========================

Dynamic truth table
-------------------

The header ``<kitty/dynamic_truth_table.hpp>`` implements a dynamic
truth table.  A dynamic truth table can be initialized with a number
of variables that is computed at runtime.

The class :cpp:class:`kitty::dynamic_truth_table` provides the
following public member functions.

+-----------------------------------+----------------------------------------------------------------------------------+
| Function                          | Description                                                                      |
+===================================+==================================================================================+
| ``dynamic_truth_table(num_vars)`` | Standard constructor.                                                            |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``construct()``                   | Constructs a new dynamic truth table instance with the same number of variables. |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``num_vars()``                    | Returns number of variables.                                                     |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``num_blocks()``                  | Returns number of blocks.                                                        |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``num_bits()``                    | Returns number of bits.                                                          |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``begin()``                       | Begin iterator to bits.                                                          |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``end()``                         | End iterator to bits.                                                            |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``rbegin()``                      | Reverse begin iterator to bits.                                                  |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``rend()``                        | Reverse end iterator to bits.                                                    |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``cbegin()``                      | Constant begin iterator to bits.                                                 |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``cend()``                        | Constant end iterator to bits.                                                   |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``crbegin()``                     | Constant reverse begin iterator to bits.                                         |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``crend()``                       | Constant reverse end iterator to bits.                                           |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``operator=(other)``              | Assignment operator.                                                             |
+-----------------------------------+----------------------------------------------------------------------------------+
| ``mask_bits()``                   | Masks the number of valid truth table bits.                                      |
+-----------------------------------+----------------------------------------------------------------------------------+

.. doxygenstruct:: kitty::dynamic_truth_table
   :members:

Static truth table
------------------

The header ``<kitty/static_truth_table.hpp>`` implements a static
truth table.  A static truth table must be initialized with a number
of variables that is computed at compile time. It performs much faster
than the dynamic truth table. Also it is optimized for a small number
of variables, i.e., up to 6 variables. Then a truth table fits into a
single block of 64 bits. The interface makes this optimization
intransparent to the user.

The class :cpp:class:`kitty::static_truth_table` provides the
following public member functions.

+--------------------------+---------------------------------------------------------------------------------+
| Function                 | Description                                                                     |
+==========================+=================================================================================+
| ``static_truth_table()`` | Standard constructor.                                                           |
+--------------------------+---------------------------------------------------------------------------------+
| ``construct()``          | Constructs a new static truth table instance with the same number of variables. |
+--------------------------+---------------------------------------------------------------------------------+
| ``num_vars()``           | Returns number of variables.                                                    |
+--------------------------+---------------------------------------------------------------------------------+
| ``num_blocks()``         | Returns number of blocks.                                                       |
+--------------------------+---------------------------------------------------------------------------------+
| ``num_bits()``           | Returns number of bits.                                                         |
+--------------------------+---------------------------------------------------------------------------------+
| ``begin()``              | Begin iterator to bits.                                                         |
+--------------------------+---------------------------------------------------------------------------------+
| ``end()``                | End iterator to bits.                                                           |
+--------------------------+---------------------------------------------------------------------------------+
| ``rbegin()``             | Reverse begin iterator to bits.                                                 |
+--------------------------+---------------------------------------------------------------------------------+
| ``rend()``               | Reverse end iterator to bits.                                                   |
+--------------------------+---------------------------------------------------------------------------------+
| ``cbegin()``             | Constant begin iterator to bits.                                                |
+--------------------------+---------------------------------------------------------------------------------+
| ``cend()``               | Constant end iterator to bits.                                                  |
+--------------------------+---------------------------------------------------------------------------------+
| ``crbegin()``            | Constant reverse begin iterator to bits.                                        |
+--------------------------+---------------------------------------------------------------------------------+
| ``crend()``              | Constant reverse end iterator to bits.                                          |
+--------------------------+---------------------------------------------------------------------------------+
| ``operator=(other)``     | Assignment operator.                                                            |
+--------------------------+---------------------------------------------------------------------------------+
| ``mask_bits()``          | Masks the number of valid truth table bits.                                     |
+--------------------------+---------------------------------------------------------------------------------+

.. doxygenstruct:: kitty::static_truth_table
   :members: