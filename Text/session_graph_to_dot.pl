#!/bin/perl

%thys = ();

print "digraph session{\n";
print "rankdir=RL; \n";
print "node shape=box3d;\n";
while (<>) {
	if (/^"([^"]*)" "([^"]*)" "([^"]*)" \+ "([^"]*)" > (("[^"]*" )*);\s*$/) {
		my $thy = $1;
		print "\"$thy\"\;\n";
		my $deps = $5;
		$thys{$thy} ++;
		for (split(" ",$deps)) {
			if (m!^".*/([^/]*)"$!) {
				my $dep = $1;
				if ($thys{$dep}) {
					print "\"$thy\" -> \"$dep\";\n"
				}
			}
		}
	}
}
print "}\n";
