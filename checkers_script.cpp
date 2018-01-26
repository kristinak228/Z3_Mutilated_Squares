/* 
 * Kristina Kolibab
 * 1/21/18
 * CS 458 - Prof Lynch
 * Assignment 2 Script
 *
 * Compiling: g++ -o checkers checkers_script.cpp -std=c++11
 */

#include <iostream>
#include <fstream>
#include <sstream>

using namespace std;

// user input for matrix size - maybe check input
int matrix_size(){
	int N;
	string sNum;
	do{
		cout << "Enter an even number N for your NxN matrix: \n";
		getline(cin, sNum);
		istringstream(sNum) >> N;
	}while(N % 2 != 0);
	cout << "You chose a " << sNum << "x" << sNum << " matrix\n";	
	
	return N;
}

// create loop for variable declarations
void create_declarations(int& N, ofstream& f){
	f << "; vij means vertical domino in ((i,j),(i,j+1))\n";
	for(int i = 1; i < N+1; ++i){
		for(int j = 1; j < N; ++j){
			f << "(declare-const v" << i << j << " Bool)\n";
		}
	}
	
	f << "\n; hij means horizontal domino in ((i,j),(i+1,j))\n";
	for(int i = 1; i < N; ++i){
		for(int j = 1; j < N+1; ++j){
			f << "(declare-const h" << i << j << " Bool)\n";
		}
	}
}

// Covering mutilation here 
int * assign_mutilated_sqrs(int& N, ofstream& f){

	int* arr = new int[4]; // need to save x/y variables and share with covers function
		
	cout << "Which two squares would you like mutilated?\n";
	for(int i = 0; i < 2; ++i){
		cout << "Enter x pos for missing sqr: ";
		string x_;
		getline(cin, x_);
		cout << "Enter y pos for missing sqr: ";
		string y_;
		getline(cin, y_);
		int x = 0;
		int y = 0;
		stringstream(x_) >> x;
		stringstream(y_) >> y;
		
		arr[i] = x;
		arr[i+2] = y;		
	
		f << "\n; sqr (" << x << "," << y << ") is mutilated, so these dominos cannot be placed\n";		

		if((x != 1) && (x != N) && (y != 1) && (y != N)){ // center most, not an edge case
			f << "(assert (and";
			f << " (not h" << x-1 << y << ")";
			f << " (not h" << x << y << ")";
			f << " (not v" << x << y-1 << ")"; 
			f << " (not v" << x << y << ")))\n"; 
		} else if((x != 1) && (x != N) && (y == 1)){ // bottom, no corner
			f << "(assert (and";
			f << " (not h" << x-1 << y << ")";
			f << " (not h" << x << y << ")"; 
			f << " (not v" << x << y << ")))\n"; 
		} else if((x != 1) && (x != N) && (y == N)){ // top, no corner
			f << "(assert (and";
			f << " (not h" << x-1 << y << ")"; 
			f << " (not h" << x << y << ")"; 
			f << " (not v" << x << y-1 << ")))\n"; 
		} else if((x == 1) && (y != 1) && (y != N)){ // left, no corner
			f << "(assert (and";
			f << " (not h" << x << y << ")";
			f << " (not v" << x << y-1 << ")";
			f << " (not v" << x << y << ")";
		} else if((x == 4) && (y != 1) && (y != N)){ // right, no corner
			f << "(assert (and";
			f << " (not h" << x-1 << y << ")";
			f << " (not v" << x << y-1 << ")";
			f << " (not v" << x << y << ")))\n";
		} else if((x == 1) && (y == N)){ // top left corner
			f << "(assert (and";
			f << " (not h" << x << y << ")";
			f << " (not v" << x << y-1 << ")))\n";
		} else if((x == N) && (y == N)){ // top right corner
			f << "(assert (and";
			f << " (not h" << x-1 << y << ")";
			f << " (not v" << x << y-1 << ")))\n";
		} else if((x == 1) && (y == 1)){ // bottom left corner
			f << "(assert (and";
			f << " (not h" << x << y << ")";
			f << " (not v" << x << y << ")))\n";
		} else if((x == N) && (y == 1)){ // bottom right corner
			f << "(assert (and";
			f << " (not h" << x-1 << y << ")";
			f << " (not v" << x << y << ")))\n";
		} else {
			cout << "Enter within range 1 - N in the x/y direction\n";
			--i;
		}
	}
	return arr;
}

// asserting that every non-mutilated sqr must be covered
void cover_all_sqrs(int& N, ofstream& f, int * arr){

	f << "\n; assert that every non-mutilated square must be covered\n";
	int i = 0;
	bool first = false;
	bool second = false;

	for(int x = 1; x <= N; ++x){
		for(int y = 1; y <= N; ++y){

			// skip if x/y is the mutilated sqr
			if((arr[i] == x) && (arr[i+2] == y)){
				if(first == false){
					++i;
					first = true;
					continue;
				} else if(second == false){
					second = true;
					continue;
				}
			} else if((x != 1) && (x != N) && (y != 1) && (y != N)){ // center most, not an edge case
				f << "(assert (or";
				f << " h" << x-1 << y;
				f << " h" << x << y;
				f << " v" << x << y-1; 
				f << " v" << x << y << "))\n"; 
			} else if((x != 1) && (x != N) && (y == 1)){ // bottom, no corner
				f << "(assert (or";
				f << " h" << x-1 << y;
				f << " h" << x << y; 
				f << " v" << x << y << "))\n"; 
			} else if((x != 1) && (x != N) && (y == 4)){ // top, no corner
				f << "(assert (or";
				f << " h" << x-1 << y; 
				f << " h" << x << y; 
				f << " v" << x << y-1 << "))\n"; 
			} else if((x == 1) && (y != 1) && (y != N)){ // left, no corner
				f << "(assert (or";
				f << " h" << x << y;
				f << " v" << x << y-1;
				f << " v" << x << y << "))\n";
			} else if((x == 4) && (y != 1) && (y != N)){ // right, no corner
				f << "(assert (or";
				f << " h" << x-1 << y;
				f << " v" << x << y-1;
				f << " v" << x << y << "))\n";
			} else if((x == 1) && (y == N)){ // top left corner
				f << "(assert (or";
				f << " h" << x << y;
				f << " v" << x << y-1 << "))\n";
			} else if((x == N) && (y == N)){ // top right corner
				f << "(assert (or";
				f << " h" << x-1 << y;
				f << " v" << x << y-1 << "))\n";
			} else if((x == 1) && (y == 1)){ // bottom left corner
				f << "(assert (or";
				f << " h" << x << y;
				f << " v" << x << y << "))\n";
			} else if((x == N) && (y == 1)){ // bottom right corner
				f << "(assert (or";
				f << " h" << x-1 << y;
				f << " v" << x << y << "))\n";
			} 
		}
	}
}

// one domino per sqrs, no overlap
void no_overlaps(int& N, ofstream& f){

	f << "\n; assert no overlap among dominos\n";

	for(int x = 1; x <= N; ++x){
		for(int y = 1; y <= N; ++y){
			if((x != 1) && (x != N) && (y != 1) && (y != N)){ // center most, not an edge case
				f << "(assert (and";
				f << " (not (and h" << x-1 << y << " v" << x << y << "))";
				f << " (not (and v" << x << y << " h" << x << y << "))";
				f << " (not (and h" << x << y << " v" << x << y-1 << "))";
				f << " (not (and v" << x << y-1 << " h" << x-1 << y << "))";
				f << " (not (and h" << x-1 << y << " h" << x << y << "))";
				f << " (not (and v" << x << y-1 << " v" << x << y << "))))\n";
			} else if((x != 1) && (x != N) && (y == 1)){ // bottom, no corner
				f << "(assert (and";
				f << " (not (and h" << x-1 << y << " v" << x << y << "))";
				f << " (not (and v" << x << y << " h" << x << y << "))"; 
				f << " (not (and h" << x-1 << y << " h" << x << y << "))))\n"; 
			} else if((x != 1) && (x != N) && (y == N)){ // top, no corner
				f << "(assert (and";
				f << " (not (and h" << x-1 << y << " h" << x << y << "))"; 
				f << " (not (and h" << x << y << " v" << x << y-1 << "))"; 
				f << " (not (and v" << x << y-1 << " h" << x-1 << y << "))))\n"; 
			} else if((x == 1) && (y != 1) && (y != N)){ // left, no corner
				f << "(assert (and";
				f << " (not (and v" << x << y-1 << " v" << x << y << "))";
				f << " (not (and v" << x << y << " h" << x << y << "))";
				f << " (not (and h" << x << y << " v" << x << y-1 << "))))\n";
			} else if((x == 4) && (y != 1) && (y != N)){ // right, no corner
				f << "(assert (and";
				f << " (not (and h" << x-1 << y << " v" << x << y << "))";
				f << " (not (and v" << x << y << " v" << x << y-1 << "))";
				f << " (not (and v" << x << y-1 << " h" << x-1 << y << "))))\n";
			} else if((x == 1) && (y == N)){ // top left corner
				f << "(assert (not (and";
				f << " h" << x << y << " v" << x << y-1 << ")))\n";
			} else if((x == N) && (y == N)){ // top right corner
				f << "(assert (not (and";
				f << " h" << x-1 << y << " v" << x << y-1 << ")))\n";
			} else if((x == 1) && (y == 1)){ // bottom left corner
				f << "(assert (not (and";
				f << " h" << x << y << " v" << x << y << ")))\n";
			} else if((x == N) && (y == 1)){ // bottom right corner
				f << "(assert (not (and";
				f << " h" << x-1 << y << " v" << x << y << ")))\n";
			}
		}
	}
} 

int main(){
	
	ofstream f;
	f.open("z3.txt");
	
//	int* arr = new int[4];

	int N = matrix_size();
	create_declarations(N, f);	
	int* arr = assign_mutilated_sqrs(N, f);
	cover_all_sqrs(N, f, arr);	
	no_overlaps(N, f);
	f << "\n(check-sat)\n";
	f << "(get-model)\n";
	
	delete[] arr;
	f.close();
	return 0;
}



