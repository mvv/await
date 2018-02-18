#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include "Rts.h"
#include "hs.await.process.h"

static int
assertDup (int fd)
{
  int dupFd = dup (fd);
  if (dupFd < 0)
    _exit (125);
  return dupFd;
}

static void
assertDup2 (int srcFd, int dstFd)
{
  if (dup2 (srcFd, dstFd) < 0)
    _exit (125);
}

pid_t
hs_await_cbits_runProcess (
  char *const argv[], char *const env[], const char *cwd,
  int *inPtr, int *outPtr, int *errPtr, int flags)
{
  int inPipe[2], outPipe[2], errPipe[2];
  int inFd = -1, outFd = -1, errFd = -1;
  int pipeInP = 0, pipeOutP = 0, pipeErrP = 0;
  int outMovedP = 0, errMovedP = 0;
  int savedErrno, fd, maxFds = -1;
  pid_t pid;

  if (inPtr)
    {
      inFd = *inPtr;
      pipeInP = inFd < 0;
    }
  if (outPtr)
    {
      outFd = *outPtr;
      pipeOutP = outFd < 0;
    }
  if (errPtr)
    {
      errFd = *errPtr;
      pipeErrP = errFd < 0;
    }

  if (pipeInP)
    {
      if (pipe (inPipe) < 0)
        return -1;

      if (inPipe[0] == inFd || inPipe[1] == inFd
          || inPipe[0] == outFd || inPipe[1] == outFd
          || inPipe[0] == errFd || inPipe[1] == errFd)
        {
          close (inPipe[0]);
          close (inPipe[1]);
          errno = EBADF;
          return -1;
        }

      if (fcntl (inPipe[1], F_SETFL, O_NONBLOCK) < 0
          || fcntl (inPipe[1], F_SETFD, FD_CLOEXEC) < 0)
        {
          savedErrno = errno;
          close (inPipe[0]);
          close (inPipe[1]);
          errno = savedErrno;
          return -1;
        }
      *inPtr = inPipe[1];
    }

  if (pipeOutP)
    {
      if (pipe (outPipe) < 0)
        {
          if (pipeInP)
            {
              savedErrno = errno;
              close (inPipe[0]);
              close (inPipe[1]);
              errno = savedErrno;
            }
          return -1;
        }

      if (outPipe[0] == inFd || outPipe[1] == inFd
          || outPipe[0] == outFd || outPipe[1] == outFd
          || outPipe[0] == errFd || outPipe[1] == errFd)
        {
          if (pipeInP)
            {
              close (inPipe[0]);
              close (inPipe[1]);
            }
          close (outPipe[0]);
          close (outPipe[1]);
          errno = EBADF;
          return -1;
        }

      if (fcntl (outPipe[0], F_SETFL, O_NONBLOCK) < 0
          || fcntl (outPipe[0], F_SETFD, FD_CLOEXEC) < 0)
        {
          savedErrno = errno;
          close (outPipe[0]);
          close (outPipe[1]);
          if (pipeInP)
            {
              close (inPipe[0]);
              close (inPipe[1]);
            }
          errno = savedErrno;
          return -1;
        }

      *outPtr = outPipe[0];
    }
  else if (outPtr)
    outFd = *outPtr;

  if (pipeErrP)
    {
      if (pipe (errPipe) < 0)
        {
          savedErrno = errno;
          if (pipeInP)
            {
              close (inPipe[0]);
              close (inPipe[1]);
            }
          if (pipeOutP)
            {
              close (outPipe[0]);
              close (outPipe[1]);
            }
          errno = savedErrno;
          return -1;
        }

      if (errPipe[0] == inFd || errPipe[1] == inFd
          || errPipe[0] == outFd || errPipe[1] == outFd
          || errPipe[0] == errFd || errPipe[1] == errFd)
        {
          if (pipeInP)
            {
              close (inPipe[0]);
              close (inPipe[1]);
            }
          if (pipeOutP)
            {
              close (outPipe[0]);
              close (outPipe[1]);
            }
          close (errPipe[0]);
          close (errPipe[1]);
          errno = EBADF;
          return -1;
        }

      if (fcntl (errPipe[0], F_SETFL, O_NONBLOCK) < 0
          || fcntl (errPipe[0], F_SETFD, FD_CLOEXEC) < 0)
        {
          savedErrno = errno;
          if (pipeInP)
            {
              close (inPipe[0]);
              close (inPipe[1]);
            }
          if (pipeOutP)
            {
              close (outPipe[0]);
              close (outPipe[1]);
            }
          close (errPipe[0]);
          close (errPipe[1]);
          errno = savedErrno;
          return -1;
        }

      *errPtr = errPipe[0];
    }

  blockUserSignals ();
  stopTimer ();

  pid = fork ();

  if (pid < 0)
    {
      savedErrno = errno;

      unblockUserSignals ();
      startTimer ();

      if (pipeInP)
        {
          close (inPipe[0]);
          close (inPipe[1]);
        }
      if (pipeOutP)
        {
          close (outPipe[0]);
          close (outPipe[1]);
        }
      if (pipeOutP)
        {
          close (outPipe[0]);
          close (outPipe[1]);
        }

      errno = savedErrno;
      return -1;
    }

  if (pid > 0)
    {
      unblockUserSignals ();
      startTimer ();

      if (pipeInP)
        close (inPipe[0]);
      if (pipeOutP)
        close (outPipe[1]);
      if (pipeErrP)
        close (errPipe[1]);

      return pid;
    }

  unblockUserSignals ();

  if (cwd && chdir (cwd) < 0)
    _exit (126);

  if (!inPtr)
    {
      inFd = open ("/dev/null", O_RDONLY);
      if (inFd < 0)
        _exit (125);
    }
  if (pipeInP)
    inFd = inPipe[0];

  if (!outPtr || !errPtr)
    {
      fd = open ("/dev/zero", O_WRONLY);
      if (fd < 0)
        _exit (125);
      if (!outPtr)
        outFd = fd;
      if (!errPtr)
        errFd = fd;
    }
  if (pipeOutP)
    outFd = outPipe[1];
  if (pipeErrP)
    errFd = errPipe[1];

  if (inFd > 0)
    {
      if (outFd == 0)
        {
          outFd = assertDup (outFd);
          outMovedP = 1;
        }
      if (errFd == 0)
        {
          errFd = assertDup (errFd);
          errMovedP = 1;
        }
      assertDup2 (inFd, 0);
    }

  if (outFd >= 0 && outFd != 1)
    {
      if (inFd == 1)
        inFd = -1;
      if (errFd == 1)
        {
          errFd = assertDup (errFd);
          errMovedP = 1;
        }
      assertDup2 (outFd, 1);
    }

  if (errFd >= 0 && errFd != 2)
    {
      if (inFd == 2)
        inFd = -1;
      if (outFd == 2)
        outFd = -1;
      assertDup2 (errFd, 2);
    }

  if ((!inPtr || pipeInP) && inFd > 0)
    {
      if (outFd == inFd)
        outFd = -1;
      if (errFd == inFd)
        errFd = -1;
      close (inFd);
    }
  if ((!outPtr || pipeOutP || outMovedP) && outFd >= 0 && outFd != 1) 
    {
      if (errFd == outFd)
        errFd = -1;
      close (outFd);
    }
  if ((!errPtr || pipeErrP || errMovedP) && errFd >= 0 && errFd != 2)
    close (errFd);

  if (flags & HS_AWAIT_PROCESS_CLOSE_FDS_FLAG)
    {
#ifdef _SC_OPEN_MAX
      maxFds = sysconf (_SC_OPEN_MAX);
#endif
      if (maxFds < 0)
        maxFds = 256;
      for (fd = 3; fd < maxFds; ++fd)
        close (fd);
    }

  if (env)
    execve (argv[0], argv, env);
  else
    execvp (argv[0], argv);

  _exit (127);
}

