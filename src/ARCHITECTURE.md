# Rationale

TML as a system needs certain visibility between different components to properly 
work: 

* driver: 

* dictionary: it keeps track of the symbol/numeric value to be used in the forthcoming
modules. It's pourpouse is to compress the information mapping lexemes to integers. 

* bdd library: Main module 

* ir_builder, 

* tables, 


It has been refactor in order to encapsulate that visibility in certain new objects
with a clear functionallity instead of allowing a shared state/control among all
components.

* builtins/builtins_factory: builtins deal with predefined actions on TML.

* constants/constants_factory

* progress monitor



+-----------------------------------------------------+

| DRIVER          +-----------------+  +-----------+  |

|                 |  FACTORIES      |  |  MONITORS |  |

|                 | +----+ +-----+  |  |  +-----+  |  |

+-----------------| | B  | | C   |  |--|  | O   |  |--+

                  | | U  | | O   |  |  |  | G   |  |   

+-----------------| | I  | | N   |  |--|  | R   |  |--+

| TABLES          | | L  | | S   |  |  |  | E   |  |  |

|                 | | T  | | T   |  |  |  | S   |  |  |

|                 | | I  | | A   |  |  |  | S   |  |  |

+-----------------| | N  | | N   |  |--|  |     |  |--+

                  | | S  | | T   |  |  |  |     |  |   

+-----------------| |    | | S   |  |--|  |     |  |--+

| BDD             | |    | |     |  |  |  |     |  |  |

|                 | +----+ +-----+  |  |  +-----+  |  |

|                 +-----------------+  +-----------+  |

+-----------------------------------------------------+