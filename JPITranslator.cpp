#define _CRT_SECURE_NO_WARNINGS

#include <tchar.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdarg.h>
#include <minmax.h>
#include <cstring>
#include <assert.h>
#include <errno.h>
#include <io.h>
#include <fcntl.h>
#include <time.h>

#include <sys/types.h>
#include <sys/stat.h>

#ifdef _DEBUG
// The .DAT file format debugging features are a bit
// confusing for the average non-programmer user, so 
// leave them turned off by default
#define DBGOPTS 1
#endif




//
// Some general helper definitions and functions
//



typedef unsigned char byte;
typedef unsigned short ushort;
typedef unsigned long ulong;

#define countof(array) (sizeof(array)/sizeof(array[0]))


// Fatal error - give message and exit
static void errexit(const char* msg, ...)
{
	assert(msg != NULL);
	va_list args;
	va_start(args, msg);
	vprintf(msg, args);
	exit(1);
}

// Helpers to swap byte order for big endian
static inline ushort byteswap(ushort w) {
	return (((w & 0xFF00) >> 8) |
		((w & 0x00FF) << 8));
}

static inline ulong byteswap(ulong dw) {
	return (((dw & 0xFF000000) >> 24) |
		((dw & 0x00FF0000) >> 8) |
		((dw & 0x0000FF00) << 8) |
		((dw & 0x000000FF) << 24));
}

// Generic bit vector manipulations
static bool testbit(const void* pv, unsigned bitoffset)
{
	assert(pv != NULL);
	assert(0 <= bitoffset && bitoffset < 128); // arbitrary limit for argument sanity checking
	return ((((byte*)pv)[bitoffset / 8] & (1 << (bitoffset % 8))) != 0);
}

static void setbit(void* pv, unsigned bitoffset)
{
	assert(pv != NULL);
	assert(0 <= bitoffset && bitoffset < 128); // arbitrary limit for argument sanity checking
	((byte*)pv)[bitoffset / 8] |= (byte)(1 << (bitoffset % 8));
}

static void clearbit(void* pv, unsigned bitoffset)
{
	assert(pv != NULL);
	assert(0 <= bitoffset && bitoffset < 128); // arbitrary limit for argument sanity checking
	((byte*)pv)[bitoffset / 8] &= ~(byte)(1 << (bitoffset % 8));
}

// Utility class to save a value and a pointer to it and later restore the value
template <class T> class pushpop {
	T savedval;
	T* savedptr;
	pushpop();											// prohibit
	pushpop(const pushpop& p);						// prohibit
	pushpop& operator=(const pushpop& p);		// prohibit
public:
	pushpop(T* ptr, T val) : savedval(*ptr), savedptr(ptr) {
		assert(ptr != NULL);
		*ptr = val;
	}
	~pushpop(void) {
		*savedptr = savedval;
	}
};



//
// Couple routines for wildcard handling
//

char** getfilelist(const char* fnam)
{
	char drive[_MAX_DRIVE] = { 0 };
	char dir[_MAX_DIR] = { 0 };
	char name[_MAX_FNAME] = { 0 };
	char ext[_MAX_EXT] = { 0 };
	char path[_MAX_PATH] = { 0 };

	_splitpath(fnam, drive, dir, name, ext);

	char** retval = NULL;
	int n = 0, nalloc = 0;

	struct _finddata_t fdata;
	intptr_t hf;
	if ((hf = _findfirst(fnam, &fdata)) == -1)
		errexit("Unable to find file %s", fnam);
	do {
		if (n >= nalloc) {
			nalloc = max(8, nalloc * 2);
			retval = (char**)realloc(retval, sizeof(char*) * nalloc);
		}
		_splitpath(fdata.name, NULL, NULL, name, ext);
		_makepath(path, drive, dir, name, ext);
		retval[n] = (char*)malloc(strlen(path) + 1);
		strcpy(retval[n++], path);
	} while (_findnext(hf, &fdata) == 0);
	_findclose(hf);
	retval[n] = NULL;
	return retval;
}

static void freelist(char** list)
{
	if (list) {
		char** p = list;
		while (*p) free(*p++);
		free(list);
	}
}







//
// Program argument flags
//

#ifdef DBGOPTS // This stuff only useful for debugging
static bool s_bDisplayHeaders = false;			// -h
static bool s_bDebugDetail = false;				// -d
static bool s_bCompareCSV = false;					// -c
static bool noflights = false;						// -n
#endif // DBGOPTS

static ushort s_nOnlyFlight = 0;					// -f
static bool s_bSuppressSuffix = false;			// -s
static bool s_bRecalcChecksums = false;   		// -r

// Set these when we determine which firmware version would apply
static ushort s_NewVersion;                     // firmware version that signifies new checksum
static const char* s_szOldVer;

static const struct {
	ushort model;
	ushort newversion;
	const char* oldverstring;
} newmodeltable[] = {
	{760,140,"139"}, // EDM-760 has different versioning stream, correct "new" version is a guess
	{0,300,"299"} // all other models what is known at this point
};


//
// File handling - just read the whole darn .DAT file into memory
//

static byte* s_pFileBytes;							// =NULL
static size_t s_nAlloc;
static size_t s_nFileBytes;
static char s_szCurrFile[_MAX_PATH];

static void read_file(const char* szFilename)
{
	assert(szFilename != NULL && strlen(szFilename));
	strcpy(s_szCurrFile, szFilename);
	int fd = _open(szFilename, _O_BINARY | _O_RDONLY);
	if (fd == -1)
		errexit("Unable to open file %s\n%s", szFilename, strerror(errno));
	struct _stat filestats;
	if (_fstat(fd, &filestats) < 0)
		errexit("Unable to get file size %s", szFilename);
	if (s_nAlloc < (size_t)filestats.st_size) {
		if (!(s_pFileBytes = (byte*)realloc(s_pFileBytes, filestats.st_size)))
			errexit("Memory allocation failed (%d bytes)", filestats.st_size);
		s_nAlloc = filestats.st_size;
	}
	if ((s_nFileBytes = _read(fd, s_pFileBytes, filestats.st_size)) <= 0)
		errexit("Error reading file %s\n%s", szFilename, strerror(errno));
	_close(fd);
}

static void setdir(const char* basenam, char* outname, size_t outsize)
{
	assert(basenam != NULL && outname != NULL && outsize >= _MAX_PATH);
	char drive[_MAX_DRIVE];
	char dir[_MAX_DIR];
	char name[_MAX_FNAME];
	char ext[_MAX_EXT];

	_splitpath(s_szCurrFile, drive, dir, NULL, NULL);
	_splitpath(basenam, NULL, NULL, name, ext);
	_makepath(outname, drive, dir, name, ext);
}

static void write_file(const char* szFilename, const void* bytes, size_t nbytes)
{
	assert(szFilename != NULL && strlen(szFilename));
	assert(bytes != NULL && nbytes > 0);
	int fd = _open(szFilename, _O_BINARY | _O_CREAT | _O_WRONLY | _O_TRUNC, _S_IWRITE);
	if (fd == -1)
		errexit("Unable to open output file %s\n%s", szFilename, strerror(errno));
	if (_write(fd, bytes, (unsigned)nbytes) != nbytes)
		errexit("Error writing file %s\n%s", szFilename, strerror(errno));
	_close(fd);
}

static void write_renamed_file(const char* szSuffix, const char* szExt)
{
	char drive[_MAX_DRIVE];
	char dir[_MAX_DIR];
	char name[_MAX_FNAME];
	char ext[_MAX_EXT];
	char newpath[_MAX_PATH];
	_splitpath(s_szCurrFile, drive, dir, name, ext);
	strcat(name, szSuffix);
	if (szExt == NULL)
		szExt = ext;
	_makepath(newpath, drive, dir, name, szExt);
	write_file(newpath, s_pFileBytes, s_nFileBytes);
}


//
// Data definitions for various records used
//

#pragma pack(push)
#pragma pack(1)


// $U record
static char tailnum[16];							// should be enough space

// $A record
static struct {
	ushort voltshi;
	ushort voltslo;
	ushort dif;
	ushort cht;
	ushort cld;
	ushort tit;
	ushort oilhi;
	ushort oillo;
} limits;

// $C record
static struct {
	ushort model;
	ulong  flags;										// configuration bit flags
	ushort unknown_value;							// maybe more bit flags?
	ushort firmware_version;						// n.nn * 100
} config;

//Decoding of the configuration bit flagss:
//-m-d fpai r2to eeee eeee eccc cccc cc-b
//
// e = egt (up to 9 cyls)
// c = cht (up to 9 cyls)
// d = probably cld
// b = bat
// o = oil
// t = tit1
// 2 = tit2
// a = OAT
// f = fuel flow
// r = CDT (also CARB - apparently it's not distinguished in the CSV output)
// i = IAT
// m = MAP
// p = RPM
// *** e and c may be swapped
// *** d and b may be swapped (but seem to always occur anyway)
// *** m, p and i may be swapped among themselves

static const int MAX_CYLS = 9;					  // up to 9 cyls possible

static inline unsigned NUMCYLS(ulong flg = config.flags) {
	ulong mask = 0x00000004;
	unsigned n = 0;
	while (n < MAX_CYLS && (flg & mask)) {
		n++;
		mask <<= 1;
	}
	return n;
}
static inline unsigned NUMENGINE() {
	return (config.model == 760) ? 2 : 1;
}
static const ulong F_BAT = 0x00000001;
static const ulong F_C1 = 0x00000004;
static const ulong F_C2 = 0x00000008;
static const ulong F_C3 = 0x00000010;
static const ulong F_C4 = 0x00000020;
static const ulong F_C5 = 0x00000040;
static const ulong F_C6 = 0x00000080;
static const ulong F_C7 = 0x00000100;
static const ulong F_C8 = 0x00000200;
static const ulong F_C9 = 0x00000400;
static const ulong F_E1 = 0x00000800;
static const ulong F_E2 = 0x00001000;
static const ulong F_E3 = 0x00002000;
static const ulong F_E4 = 0x00004000;
static const ulong F_E5 = 0x00008000;
static const ulong F_E6 = 0x00010000;
static const ulong F_E7 = 0x00020000;
static const ulong F_E8 = 0x00040000;
static const ulong F_E9 = 0x00080000;
static const ulong F_OIL = 0x00100000;
static const ulong F_T1 = 0x00200000;
static const ulong F_T2 = 0x00400000;
static const ulong F_CDT = 0x00800000;			// also CRB
static const ulong F_IAT = 0x01000000;
static const ulong F_OAT = 0x02000000;
static const ulong F_RPM = 0x04000000;
static const ulong F_FF = 0x08000000;
static const ulong F_USD = F_FF;					// duplicate
static const ulong F_CLD = 0x10000000;			// Uh - I think.
static const ulong F_MAP = 0x40000000;
static const ulong F_DIF = F_E1 | F_E2;			// DIF exists if there's more than one EGT
static const ulong F_HP = F_RPM | F_MAP | F_FF;
static const ulong F_MARK = 0x00000001;			// 1 bit always seems to exist

// quick way to define a bunch of funcs...
#define HAS(what) static inline bool HAS##what(ulong flg=config.flags) {return ((flg & F_##what) == F_##what);}
HAS(RPM)
HAS(FF)
HAS(HP)

// $F record
static struct {
	ushort warn1;
	ushort capacity;
	ushort warn2;
	ushort kf1;
	ushort kf2;
} fuel;

// $T record
static struct {
	ushort mon;
	ushort day;
	ushort yr;
	ushort hh;
	ushort mm;
	ushort unknown_value;
} timestamp;

// $L record
static ushort headerend;

// $D record
struct flight {
	ushort flightnum;
	ushort data_length; // data length is expressed as # of 16 bit words
};


// First record in each flight's data stream
struct flightheader {
	ushort flightnum;
	ulong flags;
	ushort unknown_value;							// Don't know this one yet
	ushort interval_secs;							// Hmmm... have seen some counter-examples!?
	ushort dt;											// see decode_datebits
	ushort tm;											// see decode_timebits
};


// Each record of data stream
union datarec {
	short sarray[1];									// syntactical shorthand
	struct {
		// first byte of val/sign/scale flags
		short egt[6];
		short t1;
		short t2;

		// second byte of val/sign(/scale?) flags
		short cht[6];
		short cld;
		short oil;

		// third byte of val/sign(/scale?) flags
		short mark;
		short unk_3_1;
		short cdt;
		short iat;
		short bat;
		short oat;
		short usd;
		short ff;

		// fourth byte of val/sign(/scale?) flags
		short regt[6];									// NOTE: in 7/8/9 cyl case, E7-9 and C7-9 are stored here too
		union {
			short hp;									// single engine EDM-800
			short rt1;									// twin engine EDM-760
		};
		short rt2;

		// fifth byte of val/sign(/scale?) flags
		short rcht[6];
		short rcld;
		short roil;

		// sixth byte of val/sign(/scale?) flags
		short map;										// single engine EDM-800
		short rpm;										// single engine EDM-800
		union {
			short rpm_highbyte;						// single engine EDM-800
			short rcdt;									// twin engine EDM-760
		};
		short riat;
		short unk_6_4;
		short unk_6_5;
		short rusd;
		short rff;

		short dif[2];									// HACK - this gets computed
		byte naflags[6];
	};

	datarec(void) {
		for (int i = 0; i < sizeof(*this) / sizeof(ushort); i++)
			sarray[i] = 0x00f0;
		if (NUMENGINE() == 1) {
			// seen only one example of this... unclear why it's an exception to
			// the 0xf0 initializations.
			hp = 0;
			rpm_highbyte = 0;							// really a "scale" byte
		}

		dif[0] = dif[1] = 0;
		memset(naflags, 0, sizeof(naflags));
	}

	void calcstuff(ulong configflags);

};

static const unsigned TWINJUMP = offsetof(datarec, regt) / sizeof(short); // offset of 2nd engine egt fields


// DIF is calculated
void datarec::calcstuff(ulong configflags)
{
	int nCyls = NUMCYLS(configflags);

	// max twin engine is 6 cyls per engine
	assert(nCyls <= 6 || NUMENGINE() == 1);

	for (unsigned j = 0; j < NUMENGINE(); j++) {
		short emax = -1, emin = 0x7fff;
		for (int i = 0; i < nCyls; i++) {
			// cyls 7,8 & 9 are stored in the regt field, so this hack lines 'em up
			int idx = (i < 6) ? (i + j * TWINJUMP) : (i - 6 + TWINJUMP);
			if (!testbit(naflags, idx)) {
				if (egt[idx] < emin) emin = egt[idx];
				if (egt[idx] > emax) emax = egt[idx];
			}
		}
		dif[j] = emax - emin;
	}

	if (HASRPM(configflags)) {
		rpm += (rpm_highbyte << 8);
		rpm_highbyte = 0;							// ??
	}
}


// HACK ALERT - special case for the RPM value, which seems to have the "scale" 
// in the next data field, so we need to recognize it and account for it because
// they don't make the scale's sign bit match. See the special case lines in
// parse_data() that take care of this.
static const unsigned RPM_FIELD_NUM = offsetof(datarec, rpm) / sizeof(short);
static const unsigned RPM_HIGHBYTE_FIELD_NUM = offsetof(datarec, rpm_highbyte) / sizeof(short);


//
// This table is a description of the fields in data records, with offsets and
// text headers and the like. Be sure to KEEP THE FIELDS SORTED IN ORDER OF 
// THE CSV FILE OUTPUT!!!

// a shorthand macro to save typing in the table...
#define FLG(name) #name,F_##name

static struct {
	bool bPerEngine;									// true if a val is per engine, false if just one val (EDM-760)
	int nOffset;										// offset of field in rec.sarray
	unsigned nScale;									// some are scaled by 10, most are not
	const char* szName;								// title of field in CSV file
	ulong nFeatureFlag;
	unsigned nWhichEng;								// bit flags to flag which engine the item should display for
} const fielddesc[] = {
	{true , 0, 1,FLG(E1)},
	{true , 1, 1,FLG(E2)},
	{true , 2, 1,FLG(E3)},
	{true , 3, 1,FLG(E4)},
	{true , 4, 1,FLG(E5)},
	{true , 5, 1,FLG(E6)},
	{true , TWINJUMP + 0, 1,FLG(E7)},
	{true , TWINJUMP + 1, 1,FLG(E8)},
	{true , TWINJUMP + 2, 1,FLG(E9)},
	{true , 8, 1,FLG(C1)},
	{true , 9, 1,FLG(C2)},
	{true ,10, 1,FLG(C3)},
	{true ,11, 1,FLG(C4)},
	{true ,12, 1,FLG(C5)},
	{true ,13, 1,FLG(C6)},
	{true , TWINJUMP + 3, 1,FLG(C7)},
	{true , TWINJUMP + 4, 1,FLG(C8)},
	{true , TWINJUMP + 5, 1,FLG(C9)},
	{true , 6, 1,FLG(T1)},
	{true , 7, 1,FLG(T2)},
	{true ,15, 1,FLG(OIL)},
	{true ,-1, 1,FLG(DIF)},
	{true ,14, 1,FLG(CLD)},
	{false,21, 1,FLG(OAT)},
	{true ,18, 1,FLG(CDT)},			// not sure whether these are available in the twin model
	{true ,19, 1,FLG(IAT)},
	{false,20,10,FLG(BAT),0x01},	// battery comes before FF/USD in the single models...
	{true ,23,10,FLG(FF)},
	{true ,22,10,FLG(USD)},
	{false,20,10,FLG(BAT),0x02},	// battery comes after FF/USD in the twin model... sigh
	{false,41, 1,FLG(RPM)},			// these only are available in the single EDM models
	{false,40,10,FLG(MAP)},
	{false,30, 1,FLG(HP)},

	{false,16, 1,FLG(MARK)}
};

#pragma pack(pop)

static flight flightlist[512];					// hopefully enough capacity for any single .DAT file
static unsigned s_nFlights;

static byte* s_pHeaderEnd;							// point to end of headers for later processing



// initialize various module variables
static void reset_vars()
{
	tailnum[0] = 0;
	memset(&limits, 0, sizeof(limits));
	memset(&config, 0, sizeof(config));
	memset(&fuel, 0, sizeof(fuel));
	memset(&timestamp, 0, sizeof(timestamp));
	headerend = 0;
	memset(flightlist, 0, sizeof(flightlist));
	s_nFlights = 0;
	s_pHeaderEnd = NULL;
	s_NewVersion = 0;
	s_szOldVer = NULL;
}


//
// Compute the checksum on the textual file header records
//
static void test_header_checksum(const char* line)
{
	assert(line);
	const char* endp = strrchr(line, '*');
	const char* p = line + 1;

	if (!endp || *endp != '*')
		errexit("Header checksum format error: %s\n", line);

	ushort testval;
	byte cs = 0;
	if (sscanf(endp + 1, "%hx", &testval) != 1)
		errexit("Header checksum format error: %s\n", line);
	while (p < endp)
		cs ^= *p++;
	if (testval != cs)
		errexit("Header checksum failed: %s", line);
}

//
// Helper to parse a list of short values, which is most
// of the text header records.
//
static void parseshorts(void* results, const void* line_in, unsigned count)
{
	const char* line = reinterpret_cast<const char*>(line_in);
	assert(results != NULL && count > 0);
	assert(line != NULL && *line == '$');		// start from beginning of record
	ushort* sresults = static_cast<ushort*>(results);
	line = strchr(line, ',');						// skip $X header
	for (unsigned i = 0; i < count; i++) {
		if (!sscanf(line, ",%hu", sresults + i))
			errexit("Not enough values (%d): %s\n", count, line_in);
		line = strchr(line + 1, ',');					// this will be null on last iteration
	}
}


// parse out the relevent bits of the header
static void parse_headers(void)
{
	byte* lf;
	byte* line;

	for (line = s_pFileBytes; line < s_pFileBytes + s_nFileBytes && (lf = (byte*)memchr(line, '\r', s_nFileBytes)); line = lf) {
		assert(*lf == '\r' && *(lf + 1) == '\n');
		pushpop<byte> savecr(lf, 0);				// terminate line temporarily

		lf += 2;											// point to next record

		// check the checksum
		test_header_checksum((const char*)line);

		// maybe print the line
#ifdef DBGOPTS
		if (s_bDisplayHeaders)
			printf("%s\n", line);
#endif

		// parse the pieces into separate strings, comma delimited (and strip the trailing *xx "checksum")
		if (*line != '$')
			errexit("Expected $ at beginning of record:\n --> %s", line);

		switch (*(line + 1)) {
		case 'U': // tail number
			line += 3;									// skip past comma
			int i;
			for (i = 0; i < sizeof(tailnum) - 1 && *line && *line != '*'; i++)
				tailnum[i] = *line++ ;
				tailnum[i] = 0 ;
			break;
		case 'A': // limits info
			parseshorts(&limits, line, 8);
			break;
		case 'F': // fuel flow config info
			parseshorts(&fuel, line, 5);
			break;
		case 'T': // timestamp info
			parseshorts(&timestamp, line, 6);
			break;
		case 'C': // instrument configuration info
			parseshorts(&config, line, 5);

			// find which firmware version is "new" for this model of instrument
			s_NewVersion = newmodeltable[countof(newmodeltable) - 1].newversion;
			s_szOldVer = newmodeltable[countof(newmodeltable) - 1].oldverstring;
			for (int i = 0; i < countof(newmodeltable); i++) {
				if (newmodeltable[i].model == config.model) {
					s_NewVersion = newmodeltable[i].newversion;
					s_szOldVer = newmodeltable[i].oldverstring;
					break;
				}
			}
			assert(s_NewVersion != 0 && s_szOldVer != NULL);

			// HACK - change the version now while we're pointing at it
			// in case we write this line back out using the -r program 
			// option.
			if (config.firmware_version >= s_NewVersion) {
				char* p = (char*)(line + 1);
				char* ver = strrchr(p, ',');
				char* endp = strrchr(p, '*');
				if (!ver++ || !endp) // basic error check
					break;
				while (*ver == ' ') ver++; // skip spaces
				if (endp - ver != 3) // basic error check
					break;

				memcpy(ver, s_szOldVer, 3);
				ver += 3;
				byte cs = 0;
				while (p < endp)
					cs ^= *p++;
				char buf[8];
				sprintf(buf, "%02X", cs);
				endp++;
				*endp++ = buf[0];
				*endp++ = buf[1];
			}
			break;
		case 'L': // end of headers, unknown meaning
			parseshorts(&headerend, line, 1);

			// Save end of headers for other funcs
			s_pHeaderEnd = lf;

			// NOTE: Normal exit path of function!
			return;

		case 'D': // flight info
			if (s_nFlights >= countof(flightlist))
				errexit("This program can only handle %d flights per file", countof(flightlist));
			parseshorts(&flightlist[s_nFlights++], line, 2);
			break;
		default:
			printf("Unrecognized header record:\n --> %s\n", line);
			break;
		}
	}

	// Note that this is not the typical exit path of the function, we SHOULD
	// find the 'L' record and return from there. This is the error exit path.
	errexit("Unexpected end of .DAT file");
}

static void decode_datebits(ushort dt, ushort* m, ushort* d, ushort* y)
{
	assert(m && d && y);
	// Date is coded into 16 bits as follows
	// struct {
	//		ushort day:5;
	//		ushort mon:4;
	//		ushort yr:7;
	//	};

	*d = (dt & 0x001f);
	*m = (dt & 0x01e0) >> 5;
	*y = (dt & 0xfe00) >> 9;
};

static void decode_timebits(ushort tm, ushort* h, ushort* m, ushort* s)
{
	assert(h && m && s);
	// Time is coded into 16 bits as follows
	//	struct {
	//		ushort secs:5;      // #secs / 2 is stored
	//		ushort mins:6;
	//		ushort hrs:5;
	//	};

	*s = (tm & 0x001f) * 2;
	*m = (tm & 0x07e0) >> 5;
	*h = (tm & 0xf800) >> 11;
};


// time helpers
static void cvttime(time_t t, ushort& hh, ushort& mm, ushort& ss)
{
	struct tm* tmptr = localtime(&t);
	hh = tmptr->tm_hour;
	mm = tmptr->tm_min;
	ss = tmptr->tm_sec;
}

static time_t inittime(ushort m, ushort d, ushort y, ushort hh, ushort mm, ushort ss)
{
	assert(1 <= m && m <= 12);						// input not zero based
	struct tm tmp;
	// tmp.tm_wday and tmp.tm_yday are ignored in mktime
	tmp.tm_mon = m - 1;
	tmp.tm_mday = d;
	tmp.tm_year = (y < 50) ? y + 100 : y;				// note that century issue will be a problem after 2050
	tmp.tm_sec = ss;
	tmp.tm_min = mm;
	tmp.tm_hour = hh;
	tmp.tm_isdst = -1;
	return mktime(&tmp);
}

// an alternate form
static time_t inittime(ushort dtbits, ushort tmbits)
{
	ushort m, d, y, hh, mm, ss;
	decode_datebits(dtbits, &m, &d, &y);
	decode_timebits(tmbits, &hh, &mm, &ss);
	return inittime(m, d, y, hh, mm, ss);
}


//
// Format the data record into the format of the .CSV output
//
static void formatdata(time_t t, const datarec& rec, char* outbuf, size_t outsize)
{
	assert(outbuf != NULL && outsize > 0);

	// start printing the CSV line
	size_t nout = 0;
	ushort hh, mm, ss;

	cvttime(t, hh, mm, ss);
	nout += sprintf(outbuf + nout, "\"%d:%d:%d\"", hh, mm, ss);

	for (unsigned j = 0; j < NUMENGINE(); j++) {

		// loop through each field except "MARK" (the last field)
		for (unsigned i = 0; i < countof(fielddesc) - 1; i++) {
			if (!fielddesc[i].bPerEngine && j < NUMENGINE() - 1)
				continue;
			if (fielddesc[i].nWhichEng && !(fielddesc[i].nWhichEng & (1 << j)))
				continue;
			// making the & logic equal the flags allows some of the combined flags to work (e.g. HP)
			if ((fielddesc[i].nFeatureFlag & config.flags) == fielddesc[i].nFeatureFlag) {
				int offset = fielddesc[i].nOffset;
				// yet another special case hack to cover the computed DIF field
				if (offset < 0)
					nout += sprintf(outbuf + nout, ",%d", rec.dif[j]);
				else {
					if (fielddesc[i].bPerEngine)
						offset += j * TWINJUMP;
					if (!testbit(rec.naflags, offset)) {
						short s = rec.sarray[offset];
						nout += sprintf(outbuf + nout, ",%d", s / fielddesc[i].nScale);
						if (s % fielddesc[i].nScale)
							nout += sprintf(outbuf + nout, ".%d", s % fielddesc[i].nScale);
					}
					else
						nout += sprintf(outbuf + nout, ",\"NA\"");
				}
			}
		}
	}

	// "MARK" field special case since it's output as a string not a numeric value
	nout += sprintf(outbuf + nout, ",%s\n", rec.mark ? "\"S\"" : "");

	assert(nout < outsize);
}


//
// This will handle file output to the resultant CSV file.
// It also contains the "compare CSV" logic, which
// is mostly for testing and development - open
// the "known" .CSV file and compare each line of our
// output to the "known" file. Handy to compare lots
// of data to track down those last unrecognized bits.
//

#ifdef DBGOPTS
static FILE* s_fCompareCSV;
#endif
static FILE* s_fOutputCSV;

static void opencsv(ushort flightnum)
{
	char fnam[_MAX_FNAME];
	char path[_MAX_PATH];

	sprintf(fnam, "F%05d%s.CSV", flightnum, (s_bSuppressSuffix) ? "" : "-HACK");
	setdir(fnam, path, sizeof(path));
	if (!(s_fOutputCSV = fopen(path, "w")))
		errexit("Unable to open output file %s:\n%s", path, strerror(errno));

#ifdef DBGOPTS
	if (!s_bCompareCSV)
		return;

	sprintf(fnam, "F%05d.CSV", flightnum);
	setdir(fnam, path, sizeof(path));
	if (!(s_fCompareCSV = fopen(path, "r")))
		errexit("Unable to open comparison file %s:\n%s", path, strerror(errno));
#endif // DBGOPTS
}

static void closecsv(void)
{
	if (s_fOutputCSV) {
		fclose(s_fOutputCSV);
		s_fOutputCSV = NULL;
	}
#ifdef DBGOPTS
	if (s_fCompareCSV) {
		fclose(s_fCompareCSV);
		s_fCompareCSV = NULL;
	}
#endif
}

static void outputline(const char* line, bool bsuppressdiff = false)
{
	assert(line != NULL);

	if (s_fOutputCSV)
		if (fputs(line, s_fOutputCSV) == EOF)
			errexit("Error writing output file.\n%s", strerror(errno));

#ifdef DBGOPTS
	const char* prefix = "";
	if (s_bCompareCSV) {
		if (!s_fCompareCSV)
			errexit("Comparison file not opened correctly (??)");

		char buf[512] = { 0 };
		if (!fgets(buf, sizeof(buf), s_fCompareCSV))
			errexit("Unexpected end of comparison file");

		if (strcmp(buf, line) && !bsuppressdiff) {
			prefix = "!";
			printf("%s%s", prefix, buf);
			printf("%s%s", prefix, line);
			return;
		}
	}

	if (s_bDebugDetail)
		printf("%s%s", prefix, line);
#endif
}

// Minor hack - we go through and write all the data before we know how many hours
// to put in the "Duration" line of the CSV file, so we just save where we were
// in that file and then come back to it.
static long s_DurationOffset;

static void outputheaders(const flightheader& fhead)
{
	time_t t = time(NULL);
	struct tm* tp = localtime(&t);
	char outbuf[512];
	int nout;

	sprintf(outbuf, "\"EZSave     %02d/%02d/%02d\"\n", tp->tm_mon + 1, tp->tm_mday, tp->tm_year % 100);
	outputline(outbuf, true); // ignore diffs in this line - they won't ever match
	sprintf(outbuf, "\"EDM-%4d V %3d J.P.Instruments  (C) 1998\"\n", config.model, config.firmware_version);
	outputline(outbuf);
	sprintf(outbuf, "\"Aircraft Number %s\"\n", tailnum);
	outputline(outbuf);

	ushort y, m, d;
	ushort hh, mm, ss;
	decode_datebits(fhead.dt, &m, &d, &y);
	decode_timebits(fhead.tm, &hh, &mm, &ss);
	sprintf(outbuf, "\"Flight #%d %d/%d/%d %d:%d:%d\"\n", fhead.flightnum, m, d, y, hh, mm, ss);
	outputline(outbuf);

	// UNKNOWN: There's probably a bit somewhere that the engine data is C vs F, but I haven't seen it
	const char* OAT;
	if (fhead.unknown_value & 0x20) // not 100% sure if this is the right bit, but it appears to be
		OAT = "F";
	else
		OAT = "C";
	nout = sprintf(outbuf, "\"Eng Deg F     OAT Deg %s ", OAT);
	if (HASFF(fhead.flags))
		nout += sprintf(outbuf + nout, "    F/F GPH"); // UNKNOWN: some bit somewhere probably indicates other units for FF
	nout += sprintf(outbuf + nout, "\"\n");
	outputline(outbuf);

	// See note above about fixing the Duration later.
	s_DurationOffset = ftell(s_fOutputCSV); // update duration after all data is read
	sprintf(outbuf, "\"Duration  0.00Hours   Interval %d seconds    \"\n", fhead.interval_secs);
	outputline(outbuf, true); // ignore diffs in this line - they won't match 'til later

	// write the CSV field titles
	nout = sprintf(outbuf, "\"TIME\"");
	for (unsigned j = 0; j < NUMENGINE(); j++) {
		for (unsigned i = 0; i < countof(fielddesc); i++) {
			const char* eng;
			if (!fielddesc[i].bPerEngine || NUMENGINE() == 1)
				eng = "";
			else if (j > 0)
				eng = "R";
			else
				eng = "L";
			if ((fielddesc[i].nFeatureFlag & fhead.flags) == fielddesc[i].nFeatureFlag &&
				(fielddesc[i].bPerEngine || j == NUMENGINE() - 1) &&
				(!fielddesc[i].nWhichEng || (fielddesc[i].nWhichEng & (1 << j))))
				nout += sprintf(outbuf + nout, ",\"%s%s\"", eng, fielddesc[i].szName);
		}
	}
	nout += sprintf(outbuf + nout, ",\n"); // EZSave appended an extra comma in the field names line...
	outputline(outbuf);
}

static const float SECS_PER_HOUR = (float)60.0 * (float)60.0;
static void write_duration(time_t t, const flightheader& fhead)
{
	if (!s_fOutputCSV)
		return;

	time_t start = inittime(fhead.dt, fhead.tm);
	fseek(s_fOutputCSV, s_DurationOffset, SEEK_SET);
	fprintf(s_fOutputCSV, "\"Duration %5.2f", ((float)(t - start)) / SECS_PER_HOUR);
}


#ifdef DBGOPTS
// This routine is just for dumping bits/bytes if you're scratching your head
// over the contents of the .DAT file.
static void dumpflightheader(const flightheader& fhead)
{
	ushort y, m, d;
	ushort hh, mm, ss;
	decode_datebits(fhead.dt, &m, &d, &y);
	decode_timebits(fhead.tm, &hh, &mm, &ss);
	printf("FltHdr: #%5u, flgs 0x%08x, unk %02x, secs %d, %2d/%02d/%02d %2d:%02d:%02d\n", fhead.flightnum, fhead.flags, fhead.unknown_value, fhead.interval_secs, m, d, y, hh, mm, ss);
}
#endif // DBGOPTS


//
// Checksum the various data records
//
// NOTE: This is the only change between the "new" .DAT files
// and the "old" .DAT files, i.e. they changed the XOR based
// checksum to the SUM based checksum in firmware versions after 3.00.
//

static byte calc_new_checksum(const void* pBytes, size_t nbytes)
{
	assert(pBytes && nbytes > 0);
	byte cksum = 0;
	const byte* p = reinterpret_cast<const byte*>(pBytes);
	while (nbytes-- > 0)
		cksum += *p++;
	cksum = -cksum;
	return cksum;
}

static byte calc_old_checksum(const void* pBytes, size_t nbytes)
{
	assert(pBytes && nbytes > 0);
	byte cksum = 0;
	const byte* p = reinterpret_cast<const byte*>(pBytes);
	while (nbytes-- > 0)
		cksum ^= *p++;
	return cksum;
}


static bool test_data_checksum(const void* pBytes, size_t nbytes, byte bTestCheck) {
	// ignore the firmware version - just check both, but do it in order based on
	// firmware version for efficiency in most cases
	if (config.firmware_version < s_NewVersion)
		return (calc_old_checksum(pBytes, nbytes) == bTestCheck || calc_new_checksum(pBytes, nbytes) == bTestCheck);
	else
		return (calc_new_checksum(pBytes, nbytes) == bTestCheck || calc_old_checksum(pBytes, nbytes) == bTestCheck);
}


//
// The main function for iterating through each flight and parsing out the data
//

static void parse_data(void)
{
	assert(s_pHeaderEnd != NULL);
	byte* pFlight;
	byte* pEnd;
	byte* pTop = s_pHeaderEnd;
	unsigned i;
	char outbuf[512]; // should be ample

	//
	// Iterate through every flight's data
	//
	for (unsigned iFlight = 0; iFlight < s_nFlights; pTop = pEnd, iFlight++) {

		// Point at the data for this flight (and it's end), and sanity check the length
		pFlight = pTop;
		pEnd = pFlight + flightlist[iFlight].data_length * sizeof(ushort);
		if (pEnd >= s_pFileBytes + s_nFileBytes)
			errexit("Data ends unexpectedly");
		if (pEnd - pFlight < sizeof(flightheader))
			errexit("Flight %u data length too short", flightlist[iFlight].flightnum);

		// Skip this flight if it's one we're not interested in
		if (s_nOnlyFlight && flightlist[iFlight].flightnum != s_nOnlyFlight)
			continue;

		// Note that ctor will init datarec appropriately
		datarec rec;
		time_t t;
		flightheader fhead;

		// Parse the flight header
		ushort* usarray = reinterpret_cast<ushort*>(&fhead);
		for (i = 0; i < sizeof(flightheader) / sizeof(ushort); i++) {
			usarray[i] = byteswap(*(ushort*)pFlight);
			pFlight += sizeof(ushort);
		}
		if (!test_data_checksum(&fhead, sizeof(flightheader), *pFlight++))
			errexit("Flight header checksum failed");

		// Sanity check the flight
		if (fhead.flightnum != flightlist[iFlight].flightnum)
			errexit("Flight numbers don't match (%d header, %d data), invalid file", fhead.flightnum, flightlist[iFlight].flightnum);

#ifdef DBGOPTS
		// If we care, dump some bit gunk to the screen
		if (s_bDebugDetail)
			dumpflightheader(fhead);
#endif

		// Get the time...
		t = inittime(fhead.dt, fhead.tm);

		// HACK ALERT UNTIL WE FIGURE OUT WHY THE SECONDS IS SOMETIMES ALL OUT OF WHACK!!
		// There's probably a bit field somewhere that controls this (perhaps one of the
		// bits in fhead.unknown_value?), but don't know which one yet. Given a few
		// examples it's probably not too hard to track down.
		if (fhead.interval_secs < 2 || 512 < fhead.interval_secs)
			fhead.interval_secs = 6;

		// Open the output file
		opencsv(fhead.flightnum);

		// Output the CSV headers
		outputheaders(fhead);

		// save this for various loops - syntactical shorthand
		unsigned nCyl = NUMCYLS(fhead.flags);


		//
		// Loop across each data record
		//


		// Will always read at least 3 bytes, and this ensures we don't go past
		// the end in the event that the data record ends on an odd byte count.
		// (Recall the length spec'd in the headers is given as # of 2 byte words.)
		while ((pFlight + 3) < pEnd) {

			// save top of record for later checksumming
			byte* pDataRec = pFlight;

			// Get the first flags that flag which "sets" of data are there
			byte decodeflags[2];
			byte repeatcount;
			decodeflags[0] = *pFlight++;
			decodeflags[1] = *pFlight++;

			// Get the repeat count
			repeatcount = *pFlight++;
#ifdef DBGOPTS
			if (s_bDebugDetail) // dump debugging junk if we care
				printf("decode  %02x %02x   repeat %02x\n", decodeflags[0], decodeflags[1], repeatcount);
#endif
			assert(decodeflags[0] == decodeflags[1]); // draw attention to something not seen before

			// The repeat count, if present, indicates we should just spit out the
			// previous data that many times (incrementing the timestamp appropriately).
			while (repeatcount--) {
				formatdata(t, rec, outbuf, sizeof(outbuf));
				outputline(outbuf);
				t += fhead.interval_secs;
			}

#ifdef DBGOPTS
			// More debug output handy if we are puzzling out the data file format
			if (s_bDebugDetail) {
				printf("sign/scale bytes:");
				byte* pTmp = pFlight;
				for (i = 0; i < 8; i++) {
					if (decodeflags[0] & (1 << i))
						printf(" %02x", *pTmp++);
					else
						printf("   ");
				}
				// Why only 6?? 'cause otherwise we duplicate the scale bits, I guess, and they don't ever do that.
				// Unclear on why there are two decodeflags - they always seem to be equal.
				// I've never seen scale flags for CHT or other value sets, just EGT values.
				for (i = 0; i < 6; i++) {
					if (decodeflags[1] & (1 << i))
						printf(" %02x", *pTmp++);
					else
						printf("   ");
				}
				printf("\n");
			}
#endif

			// Bit flags that indicate the existence of a given field 
			// in the compressed stream of difference values.
			byte valflags[6];
			byte scaleflags[2];						// flags presence of the EGT scale values
			byte signflags[6];						// indicates sign of dif value

			memset(valflags, 0, sizeof(valflags));
			memset(scaleflags, 0, sizeof(scaleflags));
			memset(signflags, 0, sizeof(signflags));

			// The presence of one of the bits of decodeflags indicates that
			// at least one of the group of eight fields of a "set" is present
			// and that set's flags will be present.
			for (i = 0; i < countof(valflags); i++)
				if (decodeflags[0] & (1 << i))
					valflags[i] = *pFlight++;

			// Check existence of the EGT scale value sets
			for (i = 0; i < countof(scaleflags); i++)
				if (decodeflags[0] & (0x40 << i))
					scaleflags[i] = *pFlight++;
			// never seen otherwise - draw attention to new case
			assert(scaleflags[1] == 0 || NUMENGINE() > 1);

			// Get the sign bits
			for (i = 0; i < countof(signflags); i++)
				if (decodeflags[1] & (1 << i))
					signflags[i] = *pFlight++;

			// Values are stored as 8 bit difference from previous value (except EGTs
			// which could be a 16 bit difference from previous value). Sign
			// bit determines whether the difference value is added or subtracted.
			// For the EGT/TIT fields, scale bit determines whether the high 
			// order byte of a two byte value is stored.
			//
			// Note that a difference flagged to exist but equal to zero is
			// the flag for "NA". This logic is not perfectly implemented below
			// but is hacked in to work for the most part. A little more effort
			// could refine the overall elegance a little.

			for (i = 0; i < sizeof(valflags) * 8; i++) {
				if (testbit(valflags, i)) {
					if (*pFlight == 0)
						setbit(rec.naflags, i);
					else
						clearbit(rec.naflags, i);
					if (testbit(signflags, i))
						rec.sarray[i] -= *pFlight++;
					else
						rec.sarray[i] += *pFlight++;
				}
			}

			for (unsigned j = 0; j < sizeof(scaleflags); j++) {
				for (i = 0; i < 8; i++) {
					if (testbit(scaleflags + j, i)) {
						unsigned idx = j * TWINJUMP + i;
						ushort x = *pFlight++;
						if (x != 0) {
							clearbit(rec.naflags, idx);
							x <<= 8;
							if (testbit(signflags, idx))
								rec.sarray[idx] -= x;
							else
								rec.sarray[idx] += x;
						}
						// else... note that the low byte of the dif value
						// would have set the naflags bit already if the
						// high byte and low byte were both zero
					}
				}
			}

			// HACK ALERT - special case the RPM high byte since it follows
			// the sign of the RPM field and doesn't appear to follow its
			// own sign bit.
			if (NUMENGINE() == 1) {
				if (testbit(signflags, RPM_FIELD_NUM)) {
					assert(!testbit(signflags, RPM_HIGHBYTE_FIELD_NUM));
					rec.rpm_highbyte = -rec.rpm_highbyte;
				}
				if (rec.rpm_highbyte != 0)
					clearbit(rec.naflags, RPM_FIELD_NUM);
			}

			// Compute the DIF field
			rec.calcstuff(fhead.flags);

			if (pFlight >= pEnd)
				errexit("Unexpected end of data record");
			if (!test_data_checksum(pDataRec, pFlight - pDataRec, *pFlight)) {

#ifdef DBGOPTS
				// DEBUGGING JUNK - dump the bytes of records which don't checksum correctly
				// so we can scrutinize them a bit.
				if (s_bDebugDetail) {
					int nprint = 0;
					while (pDataRec < pFlight) {
						if (!(nprint % 16))
							printf("\n%08X:", nprint);
						if (!(nprint % 2))
							printf(" ");
						printf("%02x", *pDataRec++);
						nprint++;
					}
					printf("\n");
				}
#endif

				errexit("Data checksum failed");

			}
			pFlight++;

			// Output the CSV line
			formatdata(t, rec, outbuf, sizeof(outbuf));
			outputline(outbuf);
			t += fhead.interval_secs;

		} // END WHILE() (the data record loop)

		// Go back and fix the text in the CSV headers
		write_duration(t - fhead.interval_secs /* subtract the last iteration*/, fhead);

#ifdef DBGOPTS
		if (s_bDebugDetail)
			printf("\n");
#endif

		// End of flight data, close the CSV file
		closecsv();

	}
}


//
// This corresponds to the -r flag, which will change the .DAT file to
// use the older checksum scheme and allow EZSave to work as it used to.
//
static void recompute_checksums(void)
{
	assert(s_pHeaderEnd != NULL);
	byte* pFlight;
	byte* pEnd;
	byte* pRec;
	byte* pTop = s_pHeaderEnd;
	unsigned i;

	// Note: if we don't get the new version info right
	if (config.firmware_version < s_NewVersion) {
		printf("This data file is the older version and doesn't need to be changed\n");
		return;
	}

	//
	// Iterate through every flight's data
	//
	for (unsigned iFlight = 0; iFlight < s_nFlights; pTop = pEnd, iFlight++) {

		// Point at the data for this flight (and it's end), and sanity check the length
		pFlight = pTop;
		pEnd = pFlight + flightlist[iFlight].data_length * sizeof(ushort);
		if (pEnd >= s_pFileBytes + s_nFileBytes)
			errexit("Data ends unexpectedly");
		if (pEnd - pFlight < sizeof(flightheader))
			errexit("Flight %u data length too short", flightlist[iFlight].flightnum);

		pRec = pFlight;
		pFlight += sizeof(flightheader);

		// Rechecksum the flight header
		if (!test_data_checksum(pRec, pFlight - pRec, *pFlight))
			errexit("Flight header checksum failed");

		*pFlight++ = calc_old_checksum(pRec, pFlight - pRec);


		//
		// Loop across each data record
		//


		// Will always read at least 3 bytes, and this accounts for the possibility
		// that the data record ends on an odd byte count even though the length
		// spec'd in the headers is given as # of words.
		while ((pFlight + 3) < pEnd) {

			pRec = pFlight;

			byte decodeflags[2];

			decodeflags[0] = *pFlight++;
			decodeflags[1] = *pFlight++;
			pFlight++; // repeatcount


			byte valflags[6];
			byte scaleflags[2];

			memset(valflags, 0, sizeof(valflags));
			memset(scaleflags, 0, sizeof(scaleflags));

			for (i = 0; i < countof(valflags); i++)
				if (decodeflags[0] & (1 << i))
					valflags[i] = *pFlight++;

			// Seems to be the only egt scale flags ever present (??)
			for (i = 0; i < countof(scaleflags); i++)
				if (decodeflags[0] & (0x40 << i))
					scaleflags[i] = *pFlight++;

			// never seen otherwise - draw attention to new case
			assert(scaleflags[1] == 0 || NUMENGINE() > 1);

			// These are the sign flags
			for (i = 0; i < countof(valflags); i++)
				if (decodeflags[1] & (1 << i))
					pFlight++;


			// Now just loop through the various flags, skip that many bytes,
			// and recalc the checksum when we're done.
			for (i = 0; i < sizeof(valflags) * 8; i++)
				if (testbit(valflags, i))
					pFlight++;

			for (i = 0; i < sizeof(scaleflags) * 8; i++)
				if (testbit(scaleflags, i))
					pFlight++;

			if (pFlight >= pEnd)
				errexit("Unexpected end of data record");

			if (!test_data_checksum(pRec, pFlight - pRec, *pFlight))
				errexit("Data checksum failed");

			*pFlight++ = calc_old_checksum(pRec, pFlight - pRec);

		} // END WHILE()


	}

	write_renamed_file("-HACK", ".DAT");

}

static void usage(void)
{
	printf(
#ifdef DBGOPTS
		"JPIHACK [-r] [-s] [-c] [-f#] [-h] [-d] [-n] datfiles\n"
#else
		"JPIHACK [-r] [-s] [-f#] datfiles\n"
#endif
		"\n"
		"  datfiles are a list of .DAT or .JPI files to translate, wildcards allowed.\n"
		"\n"
		"  -r      Instead of translating the .DAT file to .CSV files, this will\n"
		"          merely change the .DAT file back to the older format which is\n"
		"          supported by EZSave. This should work on files which may have\n"
		"          options that are not yet recognized by this program. The resulting\n"
		"          file will be named with the suffix -HACK (e.g. Ryymmdd-HACK.DAT).\n"
		"          In the event of .JPI file names as input, it will always output names\n"
		"          with .DAT extension names so EZSave will find them easily.\n"
		"\n"
		"  -s      Suppress CSV file name suffixing (i.e. no Fnnnnn-HACK.CSV naming)\n"
		"  -f#     Display only flight #'s data (# is numeric value)\n"
#ifdef DBGOPTS
		"  -c      Compare to existing CSV files and show diffs\n"
		"  -h      Display RAW DAT file header records\n"
		"  -d      Display detailed debugging junk\n"
		"  -n      Skip flight data (useful for debugging headers)\n"
		"\n"
		"Note that most of these options are useful for debugging the .DAT file\n"
		"format and aren't tremendously useful for everyday use.\n"
#endif
		"\n"
		"A few of the less common features of the .DAT files are not fully understood,\n"
		"so if there is some kind of translation error it could be an option\n"
		"that hasn't been seen and debugged yet. Particular cases may include recording\n"
		"engine temps in deg C, fuel flow in other than GPH, etc.\n"
		"Note that you can still use the -r option to get EZSave to work\n"
		"with your file in those cases.\n"
	);
	exit(0);
}


int main(int argc, char* argv[])
{
	int i;

	if (argc < 2)
		usage();

	for (i = 1; i < argc; i++) {
		// Note that switches only apply to files that follow them on the cmd line
		if (argv[i][0] == '-' || argv[i][0] == '/') {
			switch (tolower(argv[i][1])) {
			case '?': usage(); break;
#ifdef DBGOPTS
			case 'h': s_bDisplayHeaders = true; break;
			case 'd': s_bDebugDetail = true; break;
			case 'c': s_bCompareCSV = true; break;
			case 'n': noflights = true; break;
#endif
			case 's': s_bSuppressSuffix = true; break;
			case 'r': s_bRecalcChecksums = true; break;
			case 'f':
				if (argv[i][2])
					s_nOnlyFlight = atoi(argv[i] + 2);
				else
					errexit("-f argument must have the flight# follow without space separating it.");
				break;
			default: errexit("Unknown switch %s\n", argv[i]);
			}
		}
		else {
			// wildcards work too
			char** filelist = getfilelist(argv[i]);
			for (int j = 0; filelist[j]; j++) {
				reset_vars();
				printf("%s\n", filelist[j]);
				read_file(filelist[j]);
				parse_headers();
				if (s_bRecalcChecksums)
					recompute_checksums();
				else
#ifdef DBGOPTS
					if (!noflights)
#endif
						parse_data();
			}
			freelist(filelist);
		}
	}

	return 0;
}

