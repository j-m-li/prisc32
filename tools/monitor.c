/*
 *  26 June MMXXIV PUBLIC DOMAIN by JML
 *  The authors disclam copyright to this software
 */

#ifdef _WIN32
#include <winsock.h>
#include <windows.h>
#include <tchar.h>
#include <conio.h>
#include <stdio.h>
#include <string.h>

void print(char *p) {
	while (*p) {
		putchar(*p);
		if (*p == '\r') {
			putchar('\n');
		}
		p++;
	} 
}

int main(int argc, char *argv[])
{
	char *pcCommPort = argv[1];
	DWORD bytesRead;
	DWORD bytesWritten;
	DCB dcb;
	HANDLE hCom;
	BOOL fSuccess;
	COMMTIMEOUTS timeouts;
	char buffer[4097];
	OVERLAPPED osReader = {0};
	OVERLAPPED osWrite = {0};
	BOOL fWaitingOnRead = FALSE;

	hCom = CreateFile(pcCommPort,
					  GENERIC_READ | GENERIC_WRITE,
					  0,
					  NULL,
					  OPEN_EXISTING,
					  FILE_FLAG_OVERLAPPED,
					  NULL);
	if (hCom == INVALID_HANDLE_VALUE)
	{
		fprintf(stderr, "Cannot open serial port %s (error %lu)", argv[1], GetLastError());
		return -1;
	}
	SecureZeroMemory(&dcb, sizeof(DCB));
	dcb.DCBlength = sizeof(DCB);
	fSuccess = GetCommState(hCom, &dcb);

	if (!fSuccess)
	{
		fprintf(stderr, "Cannot get state of serial port %lu", GetLastError());
		return -1;
	}
	dcb.BaudRate = CBR_115200;
	dcb.ByteSize = 8;
	dcb.Parity = NOPARITY;
	dcb.StopBits = ONESTOPBIT;

	fSuccess = SetCommState(hCom, &dcb);

	if (!fSuccess)
	{
		fprintf(stderr, "Cannot setup serial port %lu", GetLastError());
		return -1;
	}

	fSuccess = GetCommTimeouts(hCom, &timeouts);
	if (!fSuccess)
	{
		fprintf(stderr, "Cannot get timeout serial port %lu", GetLastError());
		return -1;
	}
	timeouts.ReadIntervalTimeout = 10;
	timeouts.ReadTotalTimeoutMultiplier = 0;
	timeouts.ReadTotalTimeoutConstant = 0;
	timeouts.WriteTotalTimeoutMultiplier = 1;
	timeouts.WriteTotalTimeoutConstant = 500;
	fSuccess = SetCommTimeouts(hCom, &timeouts);
	if (!fSuccess)
	{
		fprintf(stderr, "Cannot set timeout serial port %lu", GetLastError());
		return -1;
	}
	SetCommMask(hCom, EV_RXCHAR);

	osReader.hEvent = CreateEvent(NULL, TRUE, FALSE, NULL);
	if (osReader.hEvent == NULL)
	{
		fprintf(stderr, "Cannot create event %lu", GetLastError());
		return -1;
	}
	osWrite.hEvent = CreateEvent(NULL, TRUE, FALSE, NULL);
	if (osWrite.hEvent == NULL)
	{
		fprintf(stderr, "Cannot create event %lu", GetLastError());
		return -1;
	}
	printf("press <CTRL-C> to quit\n");

	while (1)
	{
		int kb;
		bytesRead = 0;
		if (!fWaitingOnRead)
		{
			if (!ReadFile(hCom, buffer, sizeof(buffer) - 2, &bytesRead, &osReader))
			{
				if (GetLastError() != ERROR_IO_PENDING)
				{
					fprintf(stderr, "error in communication %lu", GetLastError());
				}
				else
				{
					fWaitingOnRead = TRUE;
				}
			}
			else
			{
				buffer[bytesRead] = 0;
				print(buffer);
			}
		}
		else
		{
			switch (WaitForSingleObject(osReader.hEvent, 10))
			{
			
			case WAIT_OBJECT_0:
				if (!GetOverlappedResult(hCom, &osReader, &bytesRead, FALSE))
				{
					fprintf(stderr, "error in communication %lu", GetLastError());
				}
				else
				{
					buffer[bytesRead] = 0;
					print(buffer);
				}
				fWaitingOnRead = FALSE;
				break;
			}
		}

		kb = _kbhit();
		if (kb)
		{
			buffer[0] = _getch();
			bytesWritten = 1;
			buffer[bytesWritten] = 0;
			if (!WriteFile(hCom, buffer, bytesWritten, &bytesWritten, &osWrite)) {
				if (GetLastError() != ERROR_IO_PENDING) { 
					fprintf(stderr, "error in communication %lu", GetLastError());
					exit(-1);
				} else {
					if (WAIT_OBJECT_0 == WaitForSingleObject(osWrite.hEvent, INFINITE)) {
						if (!GetOverlappedResult(hCom, &osWrite, &bytesWritten, FALSE)) {
							fprintf(stderr, "error in communication %lu", GetLastError());
							exit(-1);
						}
                    
					} else {
						fprintf(stderr, "error in communication %lu", GetLastError());
						exit(-1);
					}
				}
			}
		}
	}
	CloseHandle(hCom);
	return 0;
}

#else
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <termios.h>
#include <sys/select.h>
#include <sys/ioctl.h>

struct termios orig_termios;
struct sigaction old_action;

void reset()
{
	tcsetattr(0, TCSANOW, &orig_termios);
}

void sigint_handler(int sig_no)
{
	reset();
	sigaction(SIGINT, &old_action, NULL);
	kill(0, SIGINT);
}

int ready(int fd)
{
	struct timeval tv = {0L, 0L};
	fd_set fds;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	return select(1, &fds, NULL, NULL, &tv) > 0;
}

int main(int argc, char *argv[])
{
	char buffer[4097];
	int n;
	struct termios tty, new_termios;
	struct sigaction action;

	memset(&action, 0, sizeof(action));
	action.sa_handler = &sigint_handler;
	sigaction(SIGINT, &action, &old_action);

	int fd = open(argv[1], O_RDWR); // | O_NOCTTY | O_NDELAY);
	if (fd < 0)
	{
		perror("Cannot open serial port");
		return -1;
	}
	fcntl(fd, F_SETFL, 0);

	if (tcgetattr(fd, &tty) != 0)
	{
		perror("tcgetattr");
		return -1;
	}
	printf("\n%lx %lx %lx\n\n", (long)tty.c_iflag, (long)tty.c_oflag, (long)tty.c_lflag);

	tty.c_iflag = 0;
	tty.c_oflag = 4;
	tty.c_lflag = 0;

	cfsetospeed(&tty, B115200);
	cfsetispeed(&tty, B115200);
	tty.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL | IXON | INPCK);
	tty.c_iflag |= BRKINT;
	tty.c_cflag &= ~PARENB;
	tty.c_cflag &= ~CSTOPB;
	tty.c_cflag &= ~CSIZE;
	tty.c_cflag |= CS8;

	if (tcsetattr(fd, TCSANOW, &tty) != 0)
	{
		perror("tcsetattr");
		return -1;
	}

	/* terminal */
	tcgetattr(0, &orig_termios);
	memcpy(&new_termios, &orig_termios, sizeof(new_termios));
	atexit(reset);
	new_termios.c_lflag &= ~ICANON;
	tcsetattr(0, TCSANOW, &new_termios);

	printf("press <CTRL-C> to exit\n");
	fflush(stdout);
	while (1)
	{
		n = 0;
		ioctl(fd, FIONREAD, &n);
		if (n > 0)
		{
			n = read(fd, buffer, sizeof(buffer) - 1);
		}
		if (n > 0)
		{
			write(1, buffer, n);
		}
		if (ready(0))
		{
			read(0, buffer, 1);
			write(fd, buffer, 1);
		}
		else if (n <= 0)
		{
			usleep(10000);
		}
	}
	close(fd);
	return 0;
}
#endif
