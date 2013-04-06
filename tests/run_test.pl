#!/usr/bin/env perl

use Term::ANSIColor;
use POSIX;
use strict;

if($#ARGV < 0)
{
    print "Usage: run_test.pl test.as\n";
    exit 1;
}

my $total = 0;
my $passed = 0;

foreach(@ARGV)
{
    my $command = "";
    my $ret_exp = -1;
    my $expected = "";
    my @output = (0, "");
    my @res_files;
    my $file = $_;

    open(FILE, $file) or die "Cannot open $file";
    while(<FILE>)
    {
        if(/COMMAND=(.*?)$/)
        {
            $command = $1;
        }
        if(/EXIT=(.*?)$/)
        {
            $ret_exp = $1;
        }
        if(/EXPECTED=(.*?)$/)
        {
            $expected = $1;
        }
        if(/PRODUCES=(.*?)$/)
        {
            push(@res_files, $1);
        }
        if(/OUTPUT=(\d+?) (.+)$/)
        {
            @output = ($1, $2);
        }
    }

    if($command eq "" || $ret_exp == -1)
    {
        print color 'yellow';
        print "WARNING";
        print color 'reset';
        print ": no test information in $file\n";
        next;
    }

    $total = $total + 1;

    my $out = `exec $command $file 2>&1`;
    my $ret = $? >> 8;

    if($ret != $ret_exp)
    {
        print color 'red';
        print "FAILED";
        print color 'reset';
        print ": $file (unexpected exit value $ret, expected $ret_exp)\n";
        next;
    }

    my $out_trimmed = $out;
    my $expected_trimmed = $expected;
    $out_trimmed =~ s/( |\n)*//g;
    $expected_trimmed =~ s/( |\n)*//g;

    if($expected ne "" && !($out_trimmed =~ m/^$expected_trimmed$/))
    {
        print color 'red';
        print "FAILED";
        print color 'reset';
        print ": $file, expected output:\n\t[$expected]\n\tActual output:\n\t[$out]\n";
        next;
    }

    my $ok = 1;
    foreach my $res_info (@res_files)
    {
        my $temp_file = "";
        my $exp_file = "";

        if($res_info =~ /^(.*?) (.*?)$/)
        {
            $temp_file = $1;
            $exp_file = $2;
        }
        else
        {
            print color 'yellow';
            print "WARNING";
            print color 'reset';
            print ": syntax error in $file\n";
            next;
        }

        if(!-e $temp_file)
        {
            print color 'red';
            print "FAILED";
            print color 'reset';
            print ": $file, $temp_file does not exist\n";
            $ok = 0;
            last;
        }

        if(!-e $exp_file)
        {
            print color 'red';
            print "FAILED";
            print color 'reset';
            print ": $file, $exp_file does not exist\n";
            $ok = 0;
            last;
        }

        system("diff -iEbwB -q $temp_file $exp_file >/dev/null");
        my $ret = $? >> 8;
        if($ret != 0)
        {
            print color 'red';
            print "FAILED";
            print color 'reset';
            print ": $file, $temp_file and $exp_file are different\n";
            $ok = 0;
            last;
        }
        system("rm -f $temp_file");
    }

    next if $ok == 0;

    if($ret_exp == 0)
    {
        my $cpp_file = $file;
        my $hpp_file = $file;
        my $nob_file = $file;
        my $obj_file = $file;
        my $out_file = $file;
        my $output_file = $file;
        $cpp_file =~ s/\.as$/.cpp/;
        $hpp_file =~ s/\.as$/.hpp/;
        $nob_file =~ s/\.as$/.nob/;
        $obj_file =~ s/\.as$/.o/;
        $out_file =~ s/\.as$/.out/;
        $output_file =~ s/\.as$/.output/;

        if(!-e $cpp_file)
        {
            print color 'red';
            print "FAILED";
            print color 'reset';
            print ": $cpp_file does not exist\n";
            next;
        }

        system("g++ -c -I../lib -I../rt $cpp_file >/dev/null 2>&1; rm -f $obj_file");
        my $ret = $? >> 8;
        if($ret != 0)
        {
            print color 'red';
            print "FAILED";
            print color 'reset';
            print ": $cpp_file could not be compiled\n";
            next;
        }

        if($output[0] != 0)
        {
            if(!-e $output[1])
            {
                print color 'red';
                print "FAILED";
                print color 'reset';
                print ": $file, $output[1] does not exist\n";
                $ok = 0;
                last;
            }

            system("asc $file >/dev/null 2>&1");
            my $ret = $? >> 8;
            if($ret != 0)
            {
                print color 'red';
                print "FAILED";
                print color 'reset';
                print ": $file could not be linked\n";
                next;
            }

            system("./$out_file -c $output[0] > $output_file");
            my $ret = $? >> 8;
            if($ret != 0)
            {
                print color 'red';
                print "FAILED";
                print color 'reset';
                print ": $out_file crashed\n";
                next;
            }

            system("diff -iEbwB -q $output[1] $output_file >/dev/null");
            my $ret = $? >> 8;
            if($ret != 0)
            {
                print color 'red';
                print "FAILED";
                print color 'reset';
                print ": $file, $output[1] and $output_file are different\n";
                $ok = 0;
                next;
            }
            system("rm -f logs");
        }

        system("rm -f $cpp_file $hpp_file $nob_file $out_file");
        system("rm -f $output_file");
    }

    print color 'green';
    print "PASSED";
    print color 'reset';
    print ": $file\n";
    $passed = $passed + 1;
}

my $percent = ceil($passed / $total * 100);
print color 'bold';
print "Final results: $passed/$total passed, $percent%\n";
print color 'reset';
