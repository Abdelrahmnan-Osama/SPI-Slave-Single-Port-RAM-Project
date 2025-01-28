package slave_shared_pkg;
  typedef enum {
    IDLE,
    CHK_CMD,
    READ_ADD,
    READ_DATA,
    WRITE
  } state_e;
endpackage
