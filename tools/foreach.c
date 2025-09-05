/******************************************************************************
 *                       OS-3o3 operating system
 * 
 *               project builder using .vscode/tasks.json
 *
 *            13 Jully MMXXV PUBLIC DOMAIN by Jean-Marc Lienher
 *
 *        The authors disclaim copyright and patents to this software.
 * 
 *****************************************************************************/
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#ifdef _WIN32
#include <direct.h>
#include <process.h>
#elif defined(__APPLE__) && defined(__MACH__)
#include <TargetConditionals.h>
#include <unistd.h>
#else
#include <unistd.h>
#include <wait.h>
#endif

#define MAX_COMMAND 32000


int run(char *template, char *file)
{
	int i;
	int j;
	int l;
	static char cmd[MAX_COMMAND + 8];
	int c = 0;
	char *p;
	char *e;
	l = strlen(template);
	for (i = 0; i < l; i++) {
		if (template[i] == '$') {
			i++;
			if (template[i] == '{') {
				i++;
				j = 0;
#ifndef _WIN32
				cmd[c] = '"';
				c++;
#endif
				if (!strncmp("name}", template + i, 5)) {
					i += 5;
					while ((c < MAX_COMMAND) && file[j]) {
#ifndef _WIN32
						if (file[j] == '"' ||
							file[j] == '\\') 
						{
							cmd[c] = '\\';
							c++;
						}
#endif
						cmd[c] = file[j];
						c++;
						j++;
					}
					cmd[c] = 0;
				} else if (!strncmp("nameBasename", 
							template + i, 12)) 
				{
					i += 12;
					e = NULL;
					p = strrchr(file, '/');
					if (!p) {
						p = strrchr(file, '\\');
					}
					if (p) {
						p++;
					} else {
						p = file;
					}
					if (template[i] == '}') {
						i++;
					} else if (!strncmp("NoExtension}", 
							template + i, 12)) 
					{
						i += 12;
						e = strrchr(p, '.');
					}
					while (c < MAX_COMMAND && p[j]) {
						if (p + j == e) {
							break;
						}
#ifndef _WIN32
						if (file[j] == '"' ||
							file[j] == '\\') 
						{
							cmd[c] = '\\';
							c++;
						}
#endif
						cmd[c] = p[j];
						c++;
						j++;
					}
				} else {
					return -1;
				}
				if (c >= MAX_COMMAND + 3) {
					return -1;
				}
#ifndef _WIN32
				cmd[c] = '"';
				c++;
#endif
				cmd[c] = ' ';
				c++;
				i--;
				continue;
			} 
			cmd[c] = '$';
			c++;
		}
#ifdef _WIN32
		if (template[i] == '\\' && (template[i+1] == '"' || template[i+1] == '\\')) {
		} else {
			cmd[c] = template[i];
			c++;
		}
#else
		cmd[c] = template[i];
		c++;
#endif
		if (c >= MAX_COMMAND) {
			return -1;
		}
	}
	cmd[c]= 0;
	return system(cmd);
}

int main(int argc, char *argv[])
{
	int i;
	for (i = 2; i < argc; i++) {
		run(argv[1], argv[i]);
	}
	return 0;
}

