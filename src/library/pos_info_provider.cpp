/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/pos_info_provider.h"

namespace lean {
struct expr_ptr_eq {
    bool operator()(expr const & e1, expr const & e2) const { return e1.raw() == e2.raw(); }
};

typedef std::unordered_map<expr, pos_info, expr_hash, expr_ptr_eq> pos_table;

static pos_table * g_pos_table;
static mutex *     g_pos_table_mutex;

expr save_pos(expr const & e, pos_info const & pos) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    g_pos_table->insert(mk_pair(e, pos));
    return e;
}

expr copy_pos(expr const & src, expr const & dest) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    auto it = g_pos_table->find(src);
    if (it != g_pos_table->end())
        g_pos_table->insert(mk_pair(dest, it->second));
    return dest;
}

void erase_pos(expr const & e) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    g_pos_table->erase(e);
}

optional<pos_info> get_pos(expr const & e) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    auto it = g_pos_table->find(e);
    if (it != g_pos_table->end())
        return optional<pos_info>(it->second);
    return optional<pos_info>();
}

void reset_positions() {
    lock_guard<mutex> _(*g_pos_table_mutex);
    g_pos_table->clear();
}

char const * pos_info_provider::get_file_name() const {
    return "unknown";
}

format pos_info_provider::pp(expr const & e) const {
    try {
        auto p = get_pos_info_or_some(e);
        return format(get_file_name()) + colon() + format(p.first) + colon() + format(p.second) + colon();
    } catch (exception &) {
        return format();
    }
}

void initialize_pos_info_provider() {
    g_pos_table = new pos_table();
    g_pos_table_mutex = new mutex;
}

void finalize_pos_info_provider() {
    delete g_pos_table;
    delete g_pos_table_mutex;
}
}
