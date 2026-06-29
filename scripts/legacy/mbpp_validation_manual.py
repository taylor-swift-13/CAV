"""Manual C translations for MBPP validation tasks not covered by the AST translator."""

from __future__ import annotations


COMMON_PRELUDE = r"""
void *malloc(unsigned long size);

typedef struct {
    int *data;
    int size;
} IntArray;

typedef struct {
    double *data;
    int size;
} DoubleArray;

typedef struct {
    char *data;
    int size;
} CharArray;

typedef struct {
    char **data;
    int size;
} StringArray;

typedef struct {
    int **rows;
    int *sizes;
    int rows_count;
} IntMatrix;

typedef struct {
    char ***rows;
    int *sizes;
    int rows_count;
} StringMatrix;

typedef struct {
    int first;
    int second;
} IntPair;

typedef struct {
    int key;
    int value;
} IntCountEntry;

typedef struct {
    IntCountEntry *data;
    int size;
} IntCountMap;

typedef struct {
    int tag;
    int int_value;
    double double_value;
    char *string_value;
} MixedValue;

typedef struct {
    MixedValue *data;
    int size;
} MixedArray;

typedef struct MBPPNestedInt {
    int is_atom;
    int value;
    struct MBPPNestedInt *items;
    int size;
} MBPPNestedInt;

typedef struct {
    int is_some;
    int value;
} OptionalInt;

typedef struct {
    int is_int;
    int value;
    char *message;
} IntOrString;

typedef struct {
    int *data;
    int size;
} EmptyDictArray;

typedef struct {
    int key;
    IntArray values;
} IntListEntry;

typedef struct {
    IntListEntry *data;
    int size;
} IntListMap;

typedef struct {
    IntPair *data;
    int size;
} IntPairArray;

typedef struct {
    char *name;
    double price;
} Item;

typedef struct {
    Item *data;
    int size;
} ItemArray;

typedef struct {
    double magnitude;
    double angle;
    double rect_real;
    double rect_imag;
} PolarRectResult;

typedef struct {
    int total;
    double average;
} SumAverageResult;

typedef struct {
    int min_length;
    IntArray list;
} MinLengthResult;

typedef struct {
    int byte_size;
} AnyTuple;

static int mbpp_strlen(char *s) {
    int n = 0;
    while (s[n] != '\0') {
        n = n + 1;
    }
    return n;
}

static char *mbpp_alloc_string(int n) {
    char *out = (char *)malloc((unsigned long)(n + 1));
    out[n] = '\0';
    return out;
}

static char *mbpp_copy_string(char *s) {
    int n = mbpp_strlen(s);
    char *out = mbpp_alloc_string(n);
    for (int i = 0; i < n; i++) {
        out[i] = s[i];
    }
    return out;
}

static int mbpp_streq(char *a, char *b) {
    int i = 0;
    while (a[i] != '\0' && b[i] != '\0') {
        if (a[i] != b[i]) {
            return 0;
        }
        i = i + 1;
    }
    return a[i] == b[i];
}

static int mbpp_is_upper(char c) {
    return c >= 'A' && c <= 'Z';
}

static int mbpp_is_lower(char c) {
    return c >= 'a' && c <= 'z';
}

static int mbpp_is_digit(char c) {
    return c >= '0' && c <= '9';
}

static int mbpp_is_alnum(char c) {
    return mbpp_is_upper(c) || mbpp_is_lower(c) || mbpp_is_digit(c) || c == '_';
}

static char mbpp_to_upper(char c) {
    if (mbpp_is_lower(c)) {
        return (char)(c - ('a' - 'A'));
    }
    return c;
}

static char mbpp_to_lower(char c) {
    if (mbpp_is_upper(c)) {
        return (char)(c + ('a' - 'A'));
    }
    return c;
}

static IntArray mbpp_make_int_array(int size) {
    IntArray out;
    out.size = size;
    out.data = (int *)malloc((unsigned long)(sizeof(int) * size));
    return out;
}

static CharArray mbpp_make_char_array(int size) {
    CharArray out;
    out.size = size;
    out.data = (char *)malloc((unsigned long)(sizeof(char) * size));
    return out;
}

static StringArray mbpp_make_string_array(int size) {
    StringArray out;
    out.size = size;
    out.data = (char **)malloc((unsigned long)(sizeof(char *) * size));
    return out;
}

static IntArray mbpp_copy_int_array(int *data, int size) {
    IntArray out = mbpp_make_int_array(size);
    for (int i = 0; i < size; i++) {
        out.data[i] = data[i];
    }
    return out;
}

static void mbpp_sort_ints(int *a, int n) {
    for (int i = 1; i < n; i++) {
        int key = a[i];
        int j = i - 1;
        while (j >= 0 && a[j] > key) {
            a[j + 1] = a[j];
            j = j - 1;
        }
        a[j + 1] = key;
    }
}

static int mbpp_contains_int(int *a, int n, int x) {
    for (int i = 0; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }
    return 0;
}

static int mbpp_abs_int(int x) {
    if (x < 0) {
        return -x;
    }
    return x;
}

static int mbpp_max_int(int a, int b) {
    if (a > b) {
        return a;
    }
    return b;
}

static int mbpp_min_int(int a, int b) {
    if (a < b) {
        return a;
    }
    return b;
}

static double mbpp_sqrt_newton(double x) {
    if (x <= 0.0) {
        return 0.0;
    }
    double guess = x;
    if (guess < 1.0) {
        guess = 1.0;
    }
    for (int i = 0; i < 32; i++) {
        guess = 0.5 * (guess + x / guess);
    }
    return guess;
}

static double mbpp_round2(double x) {
    long long scaled;
    if (x >= 0.0) {
        scaled = (long long)(x * 100.0 + 0.5);
    } else {
        scaled = (long long)(x * 100.0 - 0.5);
    }
    return ((double)scaled) / 100.0;
}

static int mbpp_digits10(int x) {
    int n = 1;
    while (x >= 10) {
        x = x / 10;
        n = n + 1;
    }
    return n;
}

static char *mbpp_big_pow_decimal(int base, int exp) {
    int digits[4096];
    int len = 1;
    digits[0] = 1;
    for (int e = 0; e < exp; e++) {
        int carry = 0;
        for (int i = 0; i < len; i++) {
            int value = digits[i] * base + carry;
            digits[i] = value % 10;
            carry = value / 10;
        }
        while (carry > 0) {
            digits[len] = carry % 10;
            carry = carry / 10;
            len = len + 1;
        }
    }
    char *out = mbpp_alloc_string(len);
    for (int i = 0; i < len; i++) {
        out[i] = (char)('0' + digits[len - 1 - i]);
    }
    return out;
}

static int mbpp_word_contains_phrase(char *word, char *phrase) {
    int wn = mbpp_strlen(word);
    int pn = mbpp_strlen(phrase);
    if (pn == 0) {
        return 1;
    }
    for (int i = 0; i + pn <= wn; i++) {
        int ok = 1;
        for (int j = 0; j < pn; j++) {
            if (word[i + j] != phrase[j]) {
                ok = 0;
            }
        }
        if (ok) {
            return 1;
        }
    }
    return 0;
}

static int mbpp_write_int(char *out, int x) {
    char tmp[32];
    int n = 0;
    if (x == 0) {
        out[0] = '0';
        return 1;
    }
    if (x < 0) {
        out[0] = '-';
        return 1 + mbpp_write_int(out + 1, -x);
    }
    while (x > 0) {
        tmp[n] = (char)('0' + (x % 10));
        x = x / 10;
        n = n + 1;
    }
    for (int i = 0; i < n; i++) {
        out[i] = tmp[n - 1 - i];
    }
    return n;
}

static char *mbpp_format_range_word(int start, int end, char *text, int begin, int len) {
    char *out = mbpp_alloc_string(64 + len);
    int pos = 0;
    pos = pos + mbpp_write_int(out + pos, start);
    out[pos] = '-';
    pos = pos + 1;
    pos = pos + mbpp_write_int(out + pos, end);
    out[pos] = ':';
    out[pos + 1] = ' ';
    pos = pos + 2;
    for (int i = 0; i < len; i++) {
        out[pos + i] = text[begin + i];
    }
    out[pos + len] = '\0';
    return out;
}
"""


MANUAL_TRANSLATIONS: dict[int, dict[str, object]] = {
    512: {
        "function_name": "count_element_freq",
        "args": [("test_tuple", "MBPPNestedInt")],
        "returns": "IntCountMap",
        "code": r"""
static void mbpp_512_add_count(IntCountMap *map, int value) {
    for (int i = 0; i < map->size; i++) {
        if (map->data[i].key == value) {
            map->data[i].value = map->data[i].value + 1;
            return;
        }
    }
    map->data[map->size].key = value;
    map->data[map->size].value = 1;
    map->size = map->size + 1;
}

static void mbpp_512_flatten_count(MBPPNestedInt node, IntCountMap *map) {
    if (node.is_atom) {
        mbpp_512_add_count(map, node.value);
        return;
    }
    for (int i = 0; i < node.size; i++) {
        mbpp_512_flatten_count(node.items[i], map);
    }
}

IntCountMap mbpp_512_count_element_freq(MBPPNestedInt test_tuple) {
    IntCountMap out;
    out.data = (IntCountEntry *)malloc((unsigned long)(sizeof(IntCountEntry) * 256));
    out.size = 0;
    mbpp_512_flatten_count(test_tuple, &out);
    return out;
}
""",
    },
    513: {
        "function_name": "add_str",
        "args": [("test_tup", "List[int]"), ("K", "str")],
        "returns": "MixedArray",
        "code": r"""
MixedArray mbpp_513_add_str(int *test_tup, int test_tup_size, char *K) {
    MixedArray out;
    out.size = test_tup_size * 2;
    out.data = (MixedValue *)malloc((unsigned long)(sizeof(MixedValue) * out.size));
    for (int i = 0; i < test_tup_size; i++) {
        out.data[2 * i].tag = 0;
        out.data[2 * i].int_value = test_tup[i];
        out.data[2 * i + 1].tag = 2;
        out.data[2 * i + 1].string_value = K;
    }
    return out;
}
""",
    },
    514: {
        "function_name": "sum_elements",
        "args": [("test_tup", "List[int]")],
        "returns": "int",
        "code": r"""
int mbpp_514_sum_elements(int *test_tup, int test_tup_size) {
    int sum = 0;
    for (int i = 0; i < test_tup_size; i++) {
        sum = sum + test_tup[i];
    }
    return sum;
}
""",
    },
    515: {
        "function_name": "modular_sum",
        "args": [("arr", "List[int]"), ("n", "int"), ("m", "int")],
        "returns": "bool",
        "code": r"""
int mbpp_515_modular_sum(int *arr, int arr_size, int n, int m) {
    if (n > m) {
        return 1;
    }
    int *dp = (int *)malloc((unsigned long)(sizeof(int) * m));
    int *temp = (int *)malloc((unsigned long)(sizeof(int) * m));
    for (int i = 0; i < m; i++) {
        dp[i] = 0;
    }
    for (int i = 0; i < n; i++) {
        if (dp[0]) {
            return 1;
        }
        for (int j = 0; j < m; j++) {
            temp[j] = 0;
        }
        for (int j = 0; j < m; j++) {
            if (dp[j]) {
                int idx = (j + arr[i]) % m;
                if (!dp[idx]) {
                    temp[idx] = 1;
                }
            }
        }
        for (int j = 0; j < m; j++) {
            if (temp[j]) {
                dp[j] = 1;
            }
        }
        dp[arr[i] % m] = 1;
    }
    return dp[0];
}
""",
    },
    516: {
        "function_name": "radix_sort",
        "args": [("nums", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_516_radix_sort(int *nums, int nums_size) {
    IntArray out = mbpp_copy_int_array(nums, nums_size);
    mbpp_sort_ints(out.data, out.size);
    return out;
}
""",
    },
    518: {
        "function_name": "sqrt_root",
        "args": [("num", "int")],
        "returns": "float",
        "code": r"""
double mbpp_518_sqrt_root(int num) {
    return mbpp_sqrt_newton((double)num);
}
""",
    },
    519: {
        "function_name": "volume_tetrahedron",
        "args": [("num", "int")],
        "returns": "float",
        "code": r"""
double mbpp_519_volume_tetrahedron(int num) {
    double volume = ((double)num * (double)num * (double)num) / (6.0 * 1.4142135623730951);
    return mbpp_round2(volume);
}
""",
    },
    520: {
        "function_name": "get_lcm",
        "args": [("l", "List[int]")],
        "returns": "int",
        "code": r"""
static int mbpp_520_gcd(int a, int b) {
    while (b != 0) {
        int r = a % b;
        a = b;
        b = r;
    }
    return a;
}

static int mbpp_520_lcm(int a, int b) {
    return (a / mbpp_520_gcd(a, b)) * b;
}

int mbpp_520_get_lcm(int *l, int l_size) {
    int ans = l[0];
    for (int i = 1; i < l_size; i++) {
        ans = mbpp_520_lcm(ans, l[i]);
    }
    return ans;
}
""",
    },
    522: {
        "function_name": "lbs",
        "args": [("arr", "List[int]")],
        "returns": "int",
        "code": r"""
int mbpp_522_lbs(int *arr, int arr_size) {
    int n = arr_size;
    int *lis = (int *)malloc((unsigned long)(sizeof(int) * n));
    int *lds = (int *)malloc((unsigned long)(sizeof(int) * n));
    for (int i = 0; i < n; i++) {
        lis[i] = 1;
        lds[i] = 1;
    }
    for (int i = 1; i < n; i++) {
        for (int j = 0; j < i; j++) {
            if (arr[i] > arr[j] && lis[i] < lis[j] + 1) {
                lis[i] = lis[j] + 1;
            }
        }
    }
    for (int i = n - 2; i >= 0; i--) {
        for (int j = n - 1; j > i; j--) {
            if (arr[i] > arr[j] && lds[i] < lds[j] + 1) {
                lds[i] = lds[j] + 1;
            }
        }
    }
    int best = 0;
    for (int i = 0; i < n; i++) {
        best = mbpp_max_int(best, lis[i] + lds[i] - 1);
    }
    return best;
}
""",
    },
    523: {
        "function_name": "check_string",
        "args": [("str1", "str")],
        "returns": "List[str]",
        "code": r"""
StringArray mbpp_523_check_string(char *str1) {
    StringArray out = mbpp_make_string_array(4);
    out.size = 0;
    int has_upper = 0;
    int has_lower = 0;
    int has_digit = 0;
    int n = mbpp_strlen(str1);
    for (int i = 0; i < n; i++) {
        if (mbpp_is_upper(str1[i])) {
            has_upper = 1;
        }
        if (mbpp_is_lower(str1[i])) {
            has_lower = 1;
        }
        if (mbpp_is_digit(str1[i])) {
            has_digit = 1;
        }
    }
    if (!has_upper) {
        out.data[out.size] = "String must have 1 upper case character.";
        out.size = out.size + 1;
    }
    if (!has_lower) {
        out.data[out.size] = "String must have 1 lower case character.";
        out.size = out.size + 1;
    }
    if (!has_digit) {
        out.data[out.size] = "String must have 1 number.";
        out.size = out.size + 1;
    }
    if (n < 8) {
        out.data[out.size] = "String length should be atleast 8.";
        out.size = out.size + 1;
    }
    if (out.size == 0) {
        out.data[out.size] = "Valid string.";
        out.size = out.size + 1;
    }
    return out;
}
""",
    },
    524: {
        "function_name": "max_sum_increasing_subsequence",
        "args": [("arr", "List[int]"), ("n", "int")],
        "returns": "int",
        "code": r"""
int mbpp_524_max_sum_increasing_subsequence(int *arr, int arr_size, int n) {
    int *msis = (int *)malloc((unsigned long)(sizeof(int) * n));
    for (int i = 0; i < n; i++) {
        msis[i] = arr[i];
    }
    for (int i = 1; i < n; i++) {
        for (int j = 0; j < i; j++) {
            if (arr[i] > arr[j] && msis[i] < msis[j] + arr[i]) {
                msis[i] = msis[j] + arr[i];
            }
        }
    }
    int best = 0;
    for (int i = 0; i < n; i++) {
        best = mbpp_max_int(best, msis[i]);
    }
    return best;
}
""",
    },
    526: {
        "function_name": "capitalize_first_last_letters",
        "args": [("str1", "str")],
        "returns": "str",
        "code": r"""
char *mbpp_526_capitalize_first_last_letters(char *str1) {
    int n = mbpp_strlen(str1);
    char *out = mbpp_copy_string(str1);
    int word_start = 0;
    for (int i = 0; i <= n; i++) {
        if (str1[i] == ' ' || str1[i] == '\0') {
            int word_end = i - 1;
            if (word_start <= word_end) {
                out[word_start] = mbpp_to_upper(out[word_start]);
                out[word_end] = mbpp_to_upper(out[word_end]);
            }
            word_start = i + 1;
        }
    }
    return out;
}
""",
    },
    528: {
        "function_name": "min_length",
        "args": [("list1", "IntMatrix")],
        "returns": "MinLengthResult",
        "code": r"""
MinLengthResult mbpp_528_min_length(IntMatrix list1) {
    int best = 0;
    for (int i = 1; i < list1.rows_count; i++) {
        if (list1.sizes[i] < list1.sizes[best]) {
            best = i;
        }
    }
    MinLengthResult out;
    out.min_length = list1.sizes[best];
    out.list = mbpp_copy_int_array(list1.rows[best], list1.sizes[best]);
    return out;
}
""",
    },
    529: {
        "function_name": "jacobsthal_lucas",
        "args": [("n", "int")],
        "returns": "int",
        "code": r"""
int mbpp_529_jacobsthal_lucas(int n) {
    if (n == 0) {
        return 2;
    }
    if (n == 1) {
        return 1;
    }
    int a = 2;
    int b = 1;
    for (int i = 2; i <= n; i++) {
        int c = b + 2 * a;
        a = b;
        b = c;
    }
    return b;
}
""",
    },
    530: {
        "function_name": "negative_count",
        "args": [("nums", "List[int]")],
        "returns": "float",
        "code": r"""
double mbpp_530_negative_count(int *nums, int nums_size) {
    int negative = 0;
    for (int i = 0; i < nums_size; i++) {
        if (nums[i] < 0) {
            negative = negative + 1;
        }
    }
    return mbpp_round2(((double)negative) / ((double)nums_size));
}
""",
    },
    531: {
        "function_name": "min_coins",
        "args": [("coins", "List[int]"), ("m", "int"), ("V", "int")],
        "returns": "int",
        "code": r"""
int mbpp_531_min_coins(int *coins, int coins_size, int m, int V) {
    int *dp = (int *)malloc((unsigned long)(sizeof(int) * (V + 1)));
    for (int i = 0; i <= V; i++) {
        dp[i] = 1000000000;
    }
    dp[0] = 0;
    for (int value = 1; value <= V; value++) {
        for (int i = 0; i < m; i++) {
            if (coins[i] <= value && dp[value - coins[i]] + 1 < dp[value]) {
                dp[value] = dp[value - coins[i]] + 1;
            }
        }
    }
    return dp[V];
}
""",
    },
    532: {
        "function_name": "check_permutation",
        "args": [("str1", "str"), ("str2", "str")],
        "returns": "bool",
        "code": r"""
int mbpp_532_check_permutation(char *str1, char *str2) {
    int n1 = mbpp_strlen(str1);
    int n2 = mbpp_strlen(str2);
    if (n1 != n2) {
        return 0;
    }
    int counts[256];
    for (int i = 0; i < 256; i++) {
        counts[i] = 0;
    }
    for (int i = 0; i < n1; i++) {
        counts[(unsigned char)str1[i]] = counts[(unsigned char)str1[i]] + 1;
        counts[(unsigned char)str2[i]] = counts[(unsigned char)str2[i]] - 1;
    }
    for (int i = 0; i < 256; i++) {
        if (counts[i] != 0) {
            return 0;
        }
    }
    return 1;
}
""",
    },
    533: {
        "function_name": "remove_datatype",
        "args": [("test_tuple", "MixedArray"), ("data_type", "int")],
        "returns": "MixedArray",
        "code": r"""
MixedArray mbpp_533_remove_datatype(MixedArray test_tuple, int data_type) {
    MixedArray out;
    out.data = (MixedValue *)malloc((unsigned long)(sizeof(MixedValue) * test_tuple.size));
    out.size = 0;
    for (int i = 0; i < test_tuple.size; i++) {
        if (test_tuple.data[i].tag != data_type) {
            out.data[out.size] = test_tuple.data[i];
            out.size = out.size + 1;
        }
    }
    return out;
}
""",
    },
    534: {
        "function_name": "search_literal",
        "args": [("pattern", "str"), ("text", "str")],
        "returns": "IntPair",
        "code": r"""
IntPair mbpp_534_search_literal(char *pattern, char *text) {
    int pn = mbpp_strlen(pattern);
    int tn = mbpp_strlen(text);
    IntPair out;
    out.first = -1;
    out.second = -1;
    for (int i = 0; i + pn <= tn; i++) {
        int ok = 1;
        for (int j = 0; j < pn; j++) {
            if (text[i + j] != pattern[j]) {
                ok = 0;
            }
        }
        if (ok) {
            out.first = i;
            out.second = i + pn;
            return out;
        }
    }
    return out;
}
""",
    },
    536: {
        "function_name": "nth_items",
        "args": [("list", "List[int]"), ("n", "int")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_536_nth_items(int *list, int list_size, int n) {
    int out_size = (list_size + n - 1) / n;
    IntArray out = mbpp_make_int_array(out_size);
    int k = 0;
    for (int i = 0; i < list_size; i = i + n) {
        out.data[k] = list[i];
        k = k + 1;
    }
    return out;
}
""",
    },
    537: {
        "function_name": "first_repeated_word",
        "args": [("str1", "str")],
        "returns": "str",
        "code": r"""
char *mbpp_537_first_repeated_word(char *str1) {
    int n = mbpp_strlen(str1);
    int starts[128];
    int lens[128];
    int count = 0;
    int i = 0;
    while (i < n) {
        while (i < n && str1[i] == ' ') {
            i = i + 1;
        }
        int start = i;
        while (i < n && str1[i] != ' ') {
            i = i + 1;
        }
        int len = i - start;
        for (int w = 0; w < count; w++) {
            if (lens[w] == len) {
                int ok = 1;
                for (int j = 0; j < len; j++) {
                    if (str1[starts[w] + j] != str1[start + j]) {
                        ok = 0;
                    }
                }
                if (ok) {
                    char *out = mbpp_alloc_string(len);
                    for (int j = 0; j < len; j++) {
                        out[j] = str1[start + j];
                    }
                    return out;
                }
            }
        }
        if (len > 0) {
            starts[count] = start;
            lens[count] = len;
            count = count + 1;
        }
    }
    return "None";
}
""",
    },
    538: {
        "function_name": "string_list_to_tuple",
        "args": [("str1", "str")],
        "returns": "CharArray",
        "code": r"""
CharArray mbpp_538_string_list_to_tuple(char *str1) {
    int n = mbpp_strlen(str1);
    int count = 0;
    for (int i = 0; i < n; i++) {
        if (str1[i] != ' ') {
            count = count + 1;
        }
    }
    CharArray out = mbpp_make_char_array(count);
    int k = 0;
    for (int i = 0; i < n; i++) {
        if (str1[i] != ' ') {
            out.data[k] = str1[i];
            k = k + 1;
        }
    }
    return out;
}
""",
    },
    539: {
        "function_name": "basesnum_coresspondingnum",
        "args": [("bases_num", "List[int]"), ("index", "List[int]")],
        "returns": "List[bigint]",
        "code": r"""
StringArray mbpp_539_basesnum_coresspondingnum(int *bases_num, int bases_num_size, int *index, int index_size) {
    int n = bases_num_size;
    if (index_size < n) {
        n = index_size;
    }
    StringArray out = mbpp_make_string_array(n);
    for (int i = 0; i < n; i++) {
        out.data[i] = mbpp_big_pow_decimal(bases_num[i], index[i]);
    }
    return out;
}
""",
    },
    540: {
        "function_name": "find_Diff",
        "args": [("arr", "List[int]"), ("n", "int")],
        "returns": "int",
        "code": r"""
int mbpp_540_find_Diff(int *arr, int arr_size, int n) {
    mbpp_sort_ints(arr, n);
    int max_count = 0;
    int min_count = n;
    int count = 1;
    for (int i = 1; i <= n; i++) {
        if (i < n && arr[i] == arr[i - 1]) {
            count = count + 1;
        } else {
            if (count > max_count) {
                max_count = count;
            }
            if (count < min_count) {
                min_count = count;
            }
            count = 1;
        }
    }
    return max_count - min_count;
}
""",
    },
    542: {
        "function_name": "fill_spaces",
        "args": [("text", "str")],
        "returns": "str",
        "code": r"""
char *mbpp_542_fill_spaces(char *text) {
    int n = mbpp_strlen(text);
    char *out = mbpp_copy_string(text);
    for (int i = 0; i < n; i++) {
        if (out[i] == ' ' || out[i] == ',' || out[i] == '.') {
            out[i] = ':';
        }
    }
    return out;
}
""",
    },
    544: {
        "function_name": "flatten_tuple",
        "args": [("test_list", "StringMatrix")],
        "returns": "str",
        "code": r"""
char *mbpp_544_flatten_tuple(StringMatrix test_list) {
    int total = 0;
    int items = 0;
    for (int i = 0; i < test_list.rows_count; i++) {
        for (int j = 0; j < test_list.sizes[i]; j++) {
            total = total + mbpp_strlen(test_list.rows[i][j]);
            items = items + 1;
        }
    }
    char *out = mbpp_alloc_string(total + mbpp_max_int(0, items - 1));
    int pos = 0;
    int emitted = 0;
    for (int i = 0; i < test_list.rows_count; i++) {
        for (int j = 0; j < test_list.sizes[i]; j++) {
            if (emitted) {
                out[pos] = ' ';
                pos = pos + 1;
            }
            int n = mbpp_strlen(test_list.rows[i][j]);
            for (int k = 0; k < n; k++) {
                out[pos + k] = test_list.rows[i][j][k];
            }
            pos = pos + n;
            emitted = 1;
        }
    }
    out[pos] = '\0';
    return out;
}
""",
    },
    546: {
        "function_name": "last_occurence_char",
        "args": [("string", "str"), ("char", "char")],
        "returns": "OptionalInt",
        "code": r"""
OptionalInt mbpp_546_last_occurence_char(char *string, char char_value) {
    OptionalInt out;
    out.is_some = 0;
    out.value = 0;
    int n = mbpp_strlen(string);
    for (int i = 0; i < n; i++) {
        if (string[i] == char_value) {
            out.is_some = 1;
            out.value = i + 1;
        }
    }
    return out;
}
""",
    },
    548: {
        "function_name": "longest_increasing_subsequence",
        "args": [("arr", "List[int]")],
        "returns": "int",
        "code": r"""
int mbpp_548_longest_increasing_subsequence(int *arr, int arr_size) {
    int *dp = (int *)malloc((unsigned long)(sizeof(int) * arr_size));
    for (int i = 0; i < arr_size; i++) {
        dp[i] = 1;
    }
    for (int i = 1; i < arr_size; i++) {
        for (int j = 0; j < i; j++) {
            if (arr[i] > arr[j] && dp[i] < dp[j] + 1) {
                dp[i] = dp[j] + 1;
            }
        }
    }
    int best = 0;
    for (int i = 0; i < arr_size; i++) {
        best = mbpp_max_int(best, dp[i]);
    }
    return best;
}
""",
    },
    550: {
        "function_name": "find_Max",
        "args": [("arr", "List[int]"), ("low", "int"), ("high", "int")],
        "returns": "int",
        "code": r"""
int mbpp_550_find_Max(int *arr, int arr_size, int low, int high) {
    int best = arr[low];
    for (int i = low + 1; i <= high; i++) {
        if (arr[i] > best) {
            best = arr[i];
        }
    }
    return best;
}
""",
    },
    551: {
        "function_name": "extract_column",
        "args": [("list1", "IntMatrix"), ("n", "int")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_551_extract_column(IntMatrix list1, int n) {
    IntArray out = mbpp_make_int_array(list1.rows_count);
    for (int i = 0; i < list1.rows_count; i++) {
        out.data[i] = list1.rows[i][n];
    }
    return out;
}
""",
    },
    552: {
        "function_name": "Seq_Linear",
        "args": [("seq_nums", "List[int]")],
        "returns": "str",
        "code": r"""
char *mbpp_552_Seq_Linear(int *seq_nums, int seq_nums_size) {
    if (seq_nums_size <= 2) {
        return "Linear Sequence";
    }
    int diff = seq_nums[1] - seq_nums[0];
    for (int i = 2; i < seq_nums_size; i++) {
        if (seq_nums[i] - seq_nums[i - 1] != diff) {
            return "Non Linear Sequence";
        }
    }
    return "Linear Sequence";
}
""",
    },
    553: {
        "function_name": "tuple_to_float",
        "args": [("test_tup", "IntPair")],
        "returns": "float",
        "code": r"""
double mbpp_553_tuple_to_float(IntPair test_tup) {
    int scale = 1;
    int b = test_tup.second;
    while (scale <= b) {
        scale = scale * 10;
    }
    return (double)test_tup.first + ((double)test_tup.second) / ((double)scale);
}
""",
    },
    554: {
        "function_name": "Split",
        "args": [("list", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_554_Split(int *list, int list_size) {
    IntArray out = mbpp_make_int_array(list_size);
    out.size = 0;
    for (int i = 0; i < list_size; i++) {
        if (list[i] % 2 != 0) {
            out.data[out.size] = list[i];
            out.size = out.size + 1;
        }
    }
    return out;
}
""",
    },
    557: {
        "function_name": "toggle_string",
        "args": [("string", "str")],
        "returns": "str",
        "code": r"""
char *mbpp_557_toggle_string(char *string) {
    int n = mbpp_strlen(string);
    char *out = mbpp_copy_string(string);
    for (int i = 0; i < n; i++) {
        if (mbpp_is_upper(out[i])) {
            out[i] = mbpp_to_lower(out[i]);
        } else {
            if (mbpp_is_lower(out[i])) {
                out[i] = mbpp_to_upper(out[i]);
            }
        }
    }
    return out;
}
""",
    },
    558: {
        "function_name": "digit_distance_nums",
        "args": [("n1", "int"), ("n2", "int")],
        "returns": "int",
        "code": r"""
int mbpp_558_digit_distance_nums(int n1, int n2) {
    int x = mbpp_abs_int(n1 - n2);
    int sum = 0;
    if (x == 0) {
        return 0;
    }
    while (x > 0) {
        sum = sum + x % 10;
        x = x / 10;
    }
    return sum;
}
""",
    },
    560: {
        "function_name": "union_elements",
        "args": [("test_tup1", "List[int]"), ("test_tup2", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_560_union_elements(int *test_tup1, int test_tup1_size, int *test_tup2, int test_tup2_size) {
    IntArray out = mbpp_make_int_array(test_tup1_size + test_tup2_size);
    out.size = 0;
    for (int i = 0; i < test_tup1_size; i++) {
        if (!mbpp_contains_int(out.data, out.size, test_tup1[i])) {
            out.data[out.size] = test_tup1[i];
            out.size = out.size + 1;
        }
    }
    for (int i = 0; i < test_tup2_size; i++) {
        if (!mbpp_contains_int(out.data, out.size, test_tup2[i])) {
            out.data[out.size] = test_tup2[i];
            out.size = out.size + 1;
        }
    }
    return out;
}
""",
    },
    561: {
        "function_name": "assign_elements",
        "args": [("test_list", "List[Pair[int,int]]")],
        "returns": "IntListMap",
        "code": r"""
static int mbpp_561_find_key(IntListMap *map, int key) {
    for (int i = 0; i < map->size; i++) {
        if (map->data[i].key == key) {
            return i;
        }
    }
    map->data[map->size].key = key;
    map->data[map->size].values = mbpp_make_int_array(64);
    map->data[map->size].values.size = 0;
    map->size = map->size + 1;
    return map->size - 1;
}

IntListMap mbpp_561_assign_elements(IntPairArray test_list) {
    IntListMap out;
    out.data = (IntListEntry *)malloc((unsigned long)(sizeof(IntListEntry) * 256));
    out.size = 0;
    for (int i = 0; i < test_list.size; i++) {
        int key = test_list.data[i].first;
        int val = test_list.data[i].second;
        mbpp_561_find_key(&out, val);
        int idx = mbpp_561_find_key(&out, key);
        out.data[idx].values.data[out.data[idx].values.size] = val;
        out.data[idx].values.size = out.data[idx].values.size + 1;
    }
    return out;
}
""",
    },
    562: {
        "function_name": "Find_Max_Length",
        "args": [("lst", "IntMatrix")],
        "returns": "int",
        "code": r"""
int mbpp_562_Find_Max_Length(IntMatrix lst) {
    int best = 0;
    for (int i = 0; i < lst.rows_count; i++) {
        if (lst.sizes[i] > best) {
            best = lst.sizes[i];
        }
    }
    return best;
}
""",
    },
    563: {
        "function_name": "extract_values",
        "args": [("text", "str")],
        "returns": "List[str]",
        "code": r"""
StringArray mbpp_563_extract_values(char *text) {
    int n = mbpp_strlen(text);
    StringArray out = mbpp_make_string_array(64);
    out.size = 0;
    int i = 0;
    while (i < n) {
        while (i < n && text[i] != '"') {
            i = i + 1;
        }
        if (i >= n) {
            break;
        }
        int start = i + 1;
        i = start;
        while (i < n && text[i] != '"') {
            i = i + 1;
        }
        int len = i - start;
        char *word = mbpp_alloc_string(len);
        for (int j = 0; j < len; j++) {
            word[j] = text[start + j];
        }
        out.data[out.size] = word;
        out.size = out.size + 1;
        i = i + 1;
    }
    return out;
}
""",
    },
    565: {
        "function_name": "split",
        "args": [("word", "str")],
        "returns": "CharArray",
        "code": r"""
CharArray mbpp_565_split(char *word) {
    int n = mbpp_strlen(word);
    CharArray out = mbpp_make_char_array(n);
    for (int i = 0; i < n; i++) {
        out.data[i] = word[i];
    }
    return out;
}
""",
    },
    567: {
        "function_name": "issort_list",
        "args": [("list1", "List[int]")],
        "returns": "bool",
        "code": r"""
int mbpp_567_issort_list(int *list1, int list1_size) {
    for (int i = 0; i + 1 < list1_size; i++) {
        if (list1[i] > list1[i + 1]) {
            return 0;
        }
    }
    return 1;
}
""",
    },
    568: {
        "function_name": "empty_list",
        "args": [("length", "int")],
        "returns": "List[EmptyDict]",
        "code": r"""
EmptyDictArray mbpp_568_empty_list(int length) {
    EmptyDictArray out;
    out.size = length;
    out.data = (int *)malloc((unsigned long)(sizeof(int) * length));
    for (int i = 0; i < length; i++) {
        out.data[i] = 0;
    }
    return out;
}
""",
    },
    569: {
        "function_name": "sort_sublists",
        "args": [("list1", "StringMatrix")],
        "returns": "StringMatrix",
        "code": r"""
static int mbpp_569_str_gt(char *a, char *b) {
    int i = 0;
    while (a[i] != '\0' && b[i] != '\0') {
        if (a[i] > b[i]) {
            return 1;
        }
        if (a[i] < b[i]) {
            return 0;
        }
        i = i + 1;
    }
    return a[i] > b[i];
}

StringMatrix mbpp_569_sort_sublists(StringMatrix list1) {
    StringMatrix out;
    out.rows_count = list1.rows_count;
    out.sizes = list1.sizes;
    out.rows = (char ***)malloc((unsigned long)(sizeof(char **) * out.rows_count));
    for (int i = 0; i < out.rows_count; i++) {
        int n = list1.sizes[i];
        out.rows[i] = (char **)malloc((unsigned long)(sizeof(char *) * n));
        for (int j = 0; j < n; j++) {
            out.rows[i][j] = list1.rows[i][j];
        }
        for (int j = 1; j < n; j++) {
            char *key = out.rows[i][j];
            int k = j - 1;
            while (k >= 0 && mbpp_569_str_gt(out.rows[i][k], key)) {
                out.rows[i][k + 1] = out.rows[i][k];
                k = k - 1;
            }
            out.rows[i][k + 1] = key;
        }
    }
    return out;
}
""",
    },
    570: {
        "function_name": "remove_words",
        "args": [("list1", "List[str]"), ("charlist", "List[str]")],
        "returns": "List[str]",
        "code": r"""
StringArray mbpp_570_remove_words(StringArray list1, StringArray charlist) {
    StringArray out = mbpp_make_string_array(list1.size);
    for (int i = 0; i < list1.size; i++) {
        char *line = list1.data[i];
        int n = mbpp_strlen(line);
        char *buf = mbpp_alloc_string(n);
        int pos = 0;
        int j = 0;
        int emitted = 0;
        while (j < n) {
            while (j < n && line[j] == ' ') {
                j = j + 1;
            }
            int start = j;
            while (j < n && line[j] != ' ') {
                j = j + 1;
            }
            int len = j - start;
            char word[128];
            for (int k = 0; k < len; k++) {
                word[k] = line[start + k];
            }
            word[len] = '\0';
            int remove = 0;
            for (int c = 0; c < charlist.size; c++) {
                if (mbpp_word_contains_phrase(word, charlist.data[c])) {
                    remove = 1;
                }
            }
            if (!remove && len > 0) {
                if (emitted) {
                    buf[pos] = ' ';
                    pos = pos + 1;
                }
                for (int k = 0; k < len; k++) {
                    buf[pos + k] = word[k];
                }
                pos = pos + len;
                emitted = 1;
            }
        }
        buf[pos] = '\0';
        out.data[i] = buf;
    }
    return out;
}
""",
    },
    571: {
        "function_name": "max_sum_pair_diff_lessthan_K",
        "args": [("arr", "List[int]"), ("N", "int"), ("K", "int")],
        "returns": "int",
        "code": r"""
int mbpp_571_max_sum_pair_diff_lessthan_K(int *arr, int arr_size, int N, int K) {
    mbpp_sort_ints(arr, N);
    int *dp = (int *)malloc((unsigned long)(sizeof(int) * N));
    dp[0] = 0;
    for (int i = 1; i < N; i++) {
        dp[i] = dp[i - 1];
        if (arr[i] - arr[i - 1] < K) {
            int pair_sum = arr[i] + arr[i - 1];
            if (i >= 2) {
                pair_sum = pair_sum + dp[i - 2];
            }
            if (pair_sum > dp[i]) {
                dp[i] = pair_sum;
            }
        }
    }
    return dp[N - 1];
}
""",
    },
    572: {
        "function_name": "two_unique_nums",
        "args": [("nums", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_572_two_unique_nums(int *nums, int nums_size) {
    IntArray out = mbpp_make_int_array(nums_size);
    out.size = 0;
    for (int i = 0; i < nums_size; i++) {
        int count = 0;
        for (int j = 0; j < nums_size; j++) {
            if (nums[j] == nums[i]) {
                count = count + 1;
            }
        }
        if (count == 1) {
            out.data[out.size] = nums[i];
            out.size = out.size + 1;
        }
    }
    return out;
}
""",
    },
    573: {
        "function_name": "unique_product",
        "args": [("list_data", "List[int]")],
        "returns": "int",
        "code": r"""
int mbpp_573_unique_product(int *list_data, int list_data_size) {
    int product = 1;
    for (int i = 0; i < list_data_size; i++) {
        if (!mbpp_contains_int(list_data, i, list_data[i])) {
            product = product * list_data[i];
        }
    }
    return product;
}
""",
    },
    578: {
        "function_name": "interleave_lists",
        "args": [("list1", "List[int]"), ("list2", "List[int]"), ("list3", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_578_interleave_lists(int *list1, int list1_size, int *list2, int list2_size, int *list3, int list3_size) {
    int n = list1_size;
    IntArray out = mbpp_make_int_array(n * 3);
    for (int i = 0; i < n; i++) {
        out.data[3 * i] = list1[i];
        out.data[3 * i + 1] = list2[i];
        out.data[3 * i + 2] = list3[i];
    }
    return out;
}
""",
    },
    579: {
        "function_name": "find_dissimilar",
        "args": [("test_tup1", "List[int]"), ("test_tup2", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_579_find_dissimilar(int *test_tup1, int test_tup1_size, int *test_tup2, int test_tup2_size) {
    IntArray out = mbpp_make_int_array(test_tup1_size + test_tup2_size);
    out.size = 0;
    for (int i = 0; i < test_tup1_size; i++) {
        if (!mbpp_contains_int(test_tup2, test_tup2_size, test_tup1[i])) {
            out.data[out.size] = test_tup1[i];
            out.size = out.size + 1;
        }
    }
    for (int i = 0; i < test_tup2_size; i++) {
        if (!mbpp_contains_int(test_tup1, test_tup1_size, test_tup2[i])) {
            out.data[out.size] = test_tup2[i];
            out.size = out.size + 1;
        }
    }
    return out;
}
""",
    },
    580: {
        "function_name": "extract_even",
        "args": [("test_tuple", "MBPPNestedInt")],
        "returns": "MBPPNestedInt",
        "code": r"""
MBPPNestedInt mbpp_580_extract_even(MBPPNestedInt test_tuple) {
    MBPPNestedInt out;
    out.is_atom = 0;
    out.value = 0;
    out.items = (MBPPNestedInt *)malloc((unsigned long)(sizeof(MBPPNestedInt) * test_tuple.size));
    out.size = 0;
    for (int i = 0; i < test_tuple.size; i++) {
        MBPPNestedInt ele = test_tuple.items[i];
        if (ele.is_atom) {
            if (ele.value % 2 == 0) {
                out.items[out.size] = ele;
                out.size = out.size + 1;
            }
        } else {
            MBPPNestedInt child = mbpp_580_extract_even(ele);
            if (child.size > 0) {
                out.items[out.size] = child;
                out.size = out.size + 1;
            }
        }
    }
    return out;
}
""",
    },
    581: {
        "function_name": "surface_Area",
        "args": [("b", "int"), ("s", "int")],
        "returns": "int",
        "code": r"""
int mbpp_581_surface_Area(int b, int s) {
    return 2 * b * s + b * b;
}
""",
    },
    582: {
        "function_name": "my_dict",
        "args": [("dict_size", "int")],
        "returns": "bool",
        "code": r"""
int mbpp_582_my_dict(int dict_size) {
    if (dict_size > 0) {
        return 0;
    }
    return 1;
}
""",
    },
    584: {
        "function_name": "find_adverbs",
        "args": [("text", "str")],
        "returns": "str",
        "code": r"""
char *mbpp_584_find_adverbs(char *text) {
    int n = mbpp_strlen(text);
    int i = 0;
    while (i < n) {
        while (i < n && !mbpp_is_alnum(text[i])) {
            i = i + 1;
        }
        int start = i;
        while (i < n && mbpp_is_alnum(text[i])) {
            i = i + 1;
        }
        int end = i;
        int len = end - start;
        if (len >= 2 && text[end - 2] == 'l' && text[end - 1] == 'y') {
            return mbpp_format_range_word(start, end, text, start, len);
        }
    }
    return "";
}
""",
    },
    585: {
        "function_name": "expensive_items",
        "args": [("items", "List[Item]"), ("n", "int")],
        "returns": "List[Item]",
        "code": r"""
ItemArray mbpp_585_expensive_items(ItemArray items, int n) {
    ItemArray copy;
    copy.size = items.size;
    copy.data = (Item *)malloc((unsigned long)(sizeof(Item) * items.size));
    for (int i = 0; i < items.size; i++) {
        copy.data[i] = items.data[i];
    }
    for (int i = 1; i < copy.size; i++) {
        Item key = copy.data[i];
        int j = i - 1;
        while (j >= 0 && copy.data[j].price < key.price) {
            copy.data[j + 1] = copy.data[j];
            j = j - 1;
        }
        copy.data[j + 1] = key;
    }
    ItemArray out;
    out.size = n;
    out.data = (Item *)malloc((unsigned long)(sizeof(Item) * n));
    for (int i = 0; i < n; i++) {
        out.data[i] = copy.data[i];
    }
    return out;
}
""",
    },
    586: {
        "function_name": "split_Arr",
        "args": [("a", "List[int]"), ("n", "int"), ("k", "int")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_586_split_Arr(int *a, int a_size, int n, int k) {
    IntArray out = mbpp_make_int_array(n);
    int pos = 0;
    for (int i = k; i < n; i++) {
        out.data[pos] = a[i];
        pos = pos + 1;
    }
    for (int i = 0; i < k; i++) {
        out.data[pos] = a[i];
        pos = pos + 1;
    }
    return out;
}
""",
    },
    587: {
        "function_name": "list_tuple",
        "args": [("listx", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_587_list_tuple(int *listx, int listx_size) {
    return mbpp_copy_int_array(listx, listx_size);
}
""",
    },
    588: {
        "function_name": "big_diff",
        "args": [("nums", "List[int]")],
        "returns": "int",
        "code": r"""
int mbpp_588_big_diff(int *nums, int nums_size) {
    int lo = nums[0];
    int hi = nums[0];
    for (int i = 1; i < nums_size; i++) {
        if (nums[i] < lo) {
            lo = nums[i];
        }
        if (nums[i] > hi) {
            hi = nums[i];
        }
    }
    return hi - lo;
}
""",
    },
    589: {
        "function_name": "perfect_squares",
        "args": [("a", "int"), ("b", "int")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_589_perfect_squares(int a, int b) {
    IntArray out = mbpp_make_int_array(b - a + 1);
    out.size = 0;
    for (int i = a; i <= b; i++) {
        for (int j = 1; j * j <= i; j++) {
            if (j * j == i) {
                out.data[out.size] = i;
                out.size = out.size + 1;
            }
        }
    }
    return out;
}
""",
    },
    590: {
        "function_name": "polar_rect",
        "args": [("x", "float"), ("y", "float")],
        "returns": "PolarRectResult",
        "code": r"""
double mbpp_external_atan2(double y, double x);

PolarRectResult mbpp_590_polar_rect(double x, double y) {
    PolarRectResult out;
    out.magnitude = mbpp_sqrt_newton(x * x + y * y);
    out.angle = mbpp_external_atan2(y, x);
    out.rect_real = -2.0;
    out.rect_imag = 0.0;
    return out;
}
""",
    },
    591: {
        "function_name": "swap_List",
        "args": [("newList", "List[int]")],
        "returns": "List[int]",
        "code": r"""
IntArray mbpp_591_swap_List(int *newList, int newList_size) {
    IntArray out = mbpp_copy_int_array(newList, newList_size);
    if (out.size > 0) {
        int tmp = out.data[0];
        out.data[0] = out.data[out.size - 1];
        out.data[out.size - 1] = tmp;
    }
    return out;
}
""",
    },
    592: {
        "function_name": "sum_Of_product",
        "args": [("n", "int")],
        "returns": "int",
        "code": r"""
static int mbpp_592_binomial_Coeff(int n, int k) {
    int *C = (int *)malloc((unsigned long)(sizeof(int) * (k + 1)));
    for (int i = 0; i <= k; i++) {
        C[i] = 0;
    }
    C[0] = 1;
    for (int i = 1; i <= n; i++) {
        int limit = mbpp_min_int(i, k);
        for (int j = limit; j > 0; j--) {
            C[j] = C[j] + C[j - 1];
        }
    }
    return C[k];
}

int mbpp_592_sum_Of_product(int n) {
    return mbpp_592_binomial_Coeff(2 * n, n - 1);
}
""",
    },
    593: {
        "function_name": "removezero_ip",
        "args": [("ip", "str")],
        "returns": "str",
        "code": r"""
char *mbpp_593_removezero_ip(char *ip) {
    int n = mbpp_strlen(ip);
    char *out = mbpp_alloc_string(n);
    int pos = 0;
    for (int i = 0; i < n; i++) {
        out[pos] = ip[i];
        pos = pos + 1;
        if (ip[i] == '.') {
            while (i + 1 < n && ip[i + 1] == '0') {
                i = i + 1;
            }
        }
    }
    out[pos] = '\0';
    return out;
}
""",
    },
    594: {
        "function_name": "diff_even_odd",
        "args": [("list1", "List[int]")],
        "returns": "int",
        "code": r"""
int mbpp_594_diff_even_odd(int *list1, int list1_size) {
    int first_even = -1;
    int first_odd = -1;
    for (int i = 0; i < list1_size; i++) {
        if (first_even == -1 && list1[i] % 2 == 0) {
            first_even = list1[i];
        }
        if (first_odd == -1 && list1[i] % 2 != 0) {
            first_odd = list1[i];
        }
    }
    return first_even - first_odd;
}
""",
    },
    595: {
        "function_name": "min_Swaps",
        "args": [("str1", "str"), ("str2", "str")],
        "returns": "IntOrString",
        "code": r"""
IntOrString mbpp_595_min_Swaps(char *str1, char *str2) {
    int n = mbpp_strlen(str1);
    int count = 0;
    for (int i = 0; i < n; i++) {
        if (str1[i] != str2[i]) {
            count = count + 1;
        }
    }
    IntOrString out;
    if (count % 2 == 0) {
        out.is_int = 1;
        out.value = count / 2;
        out.message = "";
    } else {
        out.is_int = 0;
        out.value = 0;
        out.message = "Not Possible";
    }
    return out;
}
""",
    },
    596: {
        "function_name": "tuple_size",
        "args": [("tuple_list", "AnyTuple")],
        "returns": "int",
        "code": r"""
int mbpp_596_tuple_size(AnyTuple tuple_list) {
    return tuple_list.byte_size;
}
""",
    },
    597: {
        "function_name": "find_kth",
        "args": [("arr1", "List[int]"), ("arr2", "List[int]"), ("m", "int"), ("n", "int"), ("k", "int")],
        "returns": "int",
        "code": r"""
int mbpp_597_find_kth(int *arr1, int arr1_size, int *arr2, int arr2_size, int m, int n, int k) {
    int i = 0;
    int j = 0;
    int count = 0;
    int value = 0;
    while (i < m || j < n) {
        if (j >= n || (i < m && arr1[i] < arr2[j])) {
            value = arr1[i];
            i = i + 1;
        } else {
            value = arr2[j];
            j = j + 1;
        }
        count = count + 1;
        if (count == k) {
            return value;
        }
    }
    return value;
}
""",
    },
    599: {
        "function_name": "sum_average",
        "args": [("number", "int")],
        "returns": "SumAverageResult",
        "code": r"""
SumAverageResult mbpp_599_sum_average(int number) {
    SumAverageResult out;
    out.total = 0;
    for (int value = 1; value <= number; value++) {
        out.total = out.total + value;
    }
    out.average = ((double)out.total) / ((double)number);
    return out;
}
""",
    },
}


def manual_translation(task_id: int) -> dict[str, object] | None:
    item = MANUAL_TRANSLATIONS.get(task_id)
    if item is None:
        return None
    merged = dict(item)
    merged["code"] = COMMON_PRELUDE.strip() + "\n\n" + str(item["code"]).strip() + "\n"
    return merged
