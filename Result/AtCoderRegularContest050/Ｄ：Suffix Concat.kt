import java.util.Scanner
 
fun main(args: Array<String>) {
	var sc = Scanner(System.`in`)
 
	val N = sc.nextInt()
	val S = sc.next()
 
	Array(N, { Pair(it + 1, S.substring(it)) }).sortedBy { it.second }.forEach {
		println(it.first)
	}
}