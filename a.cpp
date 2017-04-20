#include <iostream>

int main() {
	const int *a = new int(1);
	int *b = static_cast<int*>(a);
	std::cout << *b;
	return 0;
}