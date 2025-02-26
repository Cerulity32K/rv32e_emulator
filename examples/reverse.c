#include <stddef.h>
#include <stdint.h>

#pragma region I/O Functions
void putchar(uint8_t ch) {
    asm volatile (
        "li a5, 0\n"
        "mv a0, %0\n"
        "ecall"
        :
        : "r" (ch)
        : "a0", "a5"
    );
}
uint8_t getchar() {
    uint8_t out;
    asm volatile (
        "li a5, 1\n"
        "ecall\n"
        "mv %0, a0"
        : "=r" (out)
        :
        : "a0", "a5"
    );
    return out;
}

void print(const char* message) {
    for (; *message; message++) {
        putchar(*message);
    }
}
#pragma endregion

// Given that BasicMemory maps the entire address space, we can choose any address we want.
// More protected or limited programs will want to use an allocator or fixed buffer.
// This is foregone for the sake of simplicity.
uint8_t* buffer = (uint8_t*)0x1000000;

int main() {
    while (1) {
        print("enter a string: ");
        uint8_t ch = getchar();
        size_t count = 0;
        while (1) {
            putchar(ch);
            if (ch == '\n') {
                break;
            // Backspace on Linux, Windows may be different.
            } else if (ch == 127) {
                print("\b \b");
                count--;
            } else {
                buffer[count] = ch;
                count++;
            }
            ch = getchar();
        }
        print("reversed string: ");
        while (count > 0) {
            putchar(buffer[--count]);
        }
        putchar('\n');
    }
}
