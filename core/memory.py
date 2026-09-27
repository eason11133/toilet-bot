"""Lightweight, dependency-free process memory instrumentation."""

import logging
import os
import sys


def process_rss_mb():
    """Return this process' resident memory in MiB, or None if unavailable."""
    try:
        try:
            import psutil
            return psutil.Process().memory_info().rss / (1024 * 1024)
        except ImportError:
            pass
        if sys.platform == "win32":
            import ctypes
            from ctypes import wintypes

            class ProcessMemoryCounters(ctypes.Structure):
                _fields_ = [
                    ("cb", wintypes.DWORD),
                    ("PageFaultCount", wintypes.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t),
                    ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t),
                    ("PeakPagefileUsage", ctypes.c_size_t),
                ]

            counters = ProcessMemoryCounters()
            counters.cb = ctypes.sizeof(counters)
            handle = ctypes.windll.kernel32.GetCurrentProcess()
            if ctypes.windll.psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
                return counters.WorkingSetSize / (1024 * 1024)
        if sys.platform.startswith("linux"):
            with open("/proc/self/statm", "r", encoding="ascii") as handle:
                resident_pages = int(handle.read().split()[1])
            return resident_pages * os.sysconf("SC_PAGE_SIZE") / (1024 * 1024)
        import resource
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return rss / 1024.0 if sys.platform != "darwin" else rss / (1024 * 1024)
    except Exception:
        return None


def log_memory(stage, **fields):
    """Log RSS and non-sensitive counters only."""
    rss = process_rss_mb()
    safe_fields = " ".join(f"{key}={value}" for key, value in fields.items())
    logging.info(
        "memory stage=%s rss_mb=%s%s",
        stage,
        f"{rss:.1f}" if rss is not None else "unavailable",
        f" {safe_fields}" if safe_fields else "",
    )
    return rss
