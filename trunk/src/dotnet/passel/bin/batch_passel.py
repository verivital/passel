import os
import argparse

Nstart = 50
Nend = 500
Nstep = 25

memtime = '/mnt/hgfs/Dropbox/Research/tools/memtime/memtime-1.3/memtime '

def callPassel(fp):
	for Ni in xrange(Nstart,Nend+1,Nstep):
		print str(Ni)
		if os.path.isfile(fp):
			command =  " passel.exe -N " + str(Ni) + " -M 6 -i " + fp
			print command

			if os.name == "nt":
				os.system(command)
			else:
				os.system(memtime + "mono " + command)	

def main(**kwargs):
	#for key, value in kwargs.iteritems():
	#	print key, value
	#cmd = '{0} {1}'.format(kwargs['program'], ' '.join(kwargs['input']))
	#cmd = '{0}'.format(kwargs['input'])
	#r = os.system(sys.argv[1], sys.argv[2])
	#print r.std_out
	#print r.std_err
	inputPath = kwargs['input'][0]
	
	if os.name == "nt":
		os.chdir("bin-win")
	else:
		os.chdir("bin-mono")
	
	inputPath = os.path.join("..", inputPath)
	if os.path.exists(inputPath):
		
		# single example
		if os.path.isfile(inputPath):
			callPassel(inputPath)
		else:	
		
			for filename in os.listdir(inputPath):
			#for dirname, dirnames, filenames in os.walk(inputPath):
				# print path to all subdirectories first.
				#for subdirname in dirnames:
				#	print os.path.join(dirname, subdirname)

				# print path to all filenames.
				#for filename in filenames:
				#print os.path.join(dirname, filename)

				#command = "passel.exe -N 3 -M 3 -i " + os.path.join(".." + os.sep + dirname, filename)
				filepath = os.path.join(inputPath, filename)
				print filepath
				callPassel(filepath)
			
	
	os.chdir(".." + os.sep)

			# Advanced usage:
			# editing the 'dirnames' list will stop os.walk() from recursing into there.
			#if '.git' in dirnames:
			# don't go into any .git directories.
			#	dirnames.remove('.git')
    

if __name__ == '__main__':
	parser = argparse.ArgumentParser(description='Get a program and run it with input', version='%(prog)s 1.0')
	#parser.add_argument('program', type=str, help='Program name')
	parser.add_argument('input', nargs='+', type=str, help='Input directory')
	#parser.add_argument('--out', type=str, default='temp.txt', help='name of output file')
	args = parser.parse_args()
	main(**vars(args))

		