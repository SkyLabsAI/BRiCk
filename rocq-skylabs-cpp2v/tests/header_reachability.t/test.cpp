#include "inc.hpp"

int root() {
    UsedRecord record{1};
    return used_function(record);
}

api::UsedInlineRecord inline_root() { return {2}; }
