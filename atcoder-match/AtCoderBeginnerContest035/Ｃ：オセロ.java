import java.util.*;
 
public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);
 
		long N = sc.nextLong();
		long Q = sc.nextLong();
 
		long array = 0;
 
		for (long i = 0; i < Q; i++) {
			long l = sc.nextLong();
			long r = sc.nextLong();
 
			long length = r - l + 1;
			long offset = N - r;
			long turn = (1 << length) - 1 << offset;
 
			array = array ^ turn;
		}
 
		long itr = 1 << N - 1;
		while (itr != 0) {
			System.out.print((array & itr) != 0 ? '1' : '0');
			itr = itr >>> 1;
		}
		System.out.println();
	}
}