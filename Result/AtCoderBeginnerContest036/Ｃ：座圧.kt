import java.util.Scanner
 
fun main(args: Array<String>) {
	var sc = Scanner(System.`in`)
 
	val N = sc.nextInt()
	val a = Array(N) { sc.nextLong() }
 
	val dict = a.toSortedSet().mapIndexed { i, l -> Pair(l, i) }.toMap()
	for (e in a) {
		println(dict[e])
	}
}