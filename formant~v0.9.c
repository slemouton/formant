/*****************formant******************************
Suivi de formants pour en echo de philippe Manoury
* original versions by bilbao and puckette
* first attempt at a formant finder/detector   
* MSP version by SLM
* 0.9 (juin 2013)
* max 6 version (64-bit)
* 0.8 (septembre 2012):
* max 5 version
* 0.5 (fevrier 2007):
* universal binary
* 0.4 (fevrier 2003):
* first distribution
* 0.3 (janvier 2003):
* debug results 
* 0.2 (novembre 2002): 
* correct autocorrelation
* dynamic allocation of buffers
* share lpc.c with lpc~
* 0.1 (octobre 98) 
*/

#include "math.h"
#include "ext.h"

#include "z_dsp.h"

#include "slm1.h"

#include "fft_mayer.proto.h"


t_class *formant_class;

#define MINPOINTS 128
#define MAXPOINTS 1024
#define WMAX 40
#define VECTOR_SIZE 64  // fixed size for ABLETON LIVE
// #define SPEC_SIZE 512 // 128
#define SAMPLE_RATE 44100
#define ONE_TWELFTH 0.083333
// #define SPEC_SIZE_MINUS_ONE 511 //127
#define RAW_FORM_NUM 4		/* number of raw formants detected */
#define FORM_NUM 3			/* number of continuously tracked ones */
#define MINPEAK 0.001			/* amplitude minimum des formants*/
#define MAXFREQ 18000			/* frequence Maximale des formants*/
#define POWER_BILBAO 0

#define VERSION "formant~ v0.91 for MSP by SLM - dsp64"
#define ALPHA_MATRIX 1

extern t_symbol s_bang;

	/*OPTI0NS :*/
#define S_OFF 0
#define S_ON 1
#define S_NEXTON 2

typedef struct peak
{
	float p_freq;
	float p_bw;
	float p_db;
	int p_status;
} t_peak;

typedef struct predictor
{
	double *inbuf_start;
	double *inbuf_end;
	double *inbuf_current;
	double *window;
	double *currentOutBuf;
	double *prevOutBuf;
	double *outbufA;
	double *outbufB;
	//double AUTO[MAXPOINTS+1];
	double *AUTO;
  	int a_s; 		//size of alpha
#if ALPHA_MATRIX
	double ALPHA[20][20];
#elif ALPHA_VECTOR
	double *ALPHA; 	// matrix
#endif
	int debugcount;			
	int debugcount2;
	int debugcount_;			
	int debugcount2_;
	int window_switch;
} t_predictor;

typedef struct ctlformant
{
	double *finalend;
	double *finalcurrent;
	double *freqlog;
	double *sinboink;
	double *cosboink;
	float *reform;	// for spectrum computation
	float *imform;	// for spectrum computation
	double *power;
	t_peak *formantout;
	float rawformant[RAW_FORM_NUM];
	void *clk;
	int uzi;		/* flag to put results out every period */
	float maxfreq;	/* max. formant frequency I care about */
	double bwscaler; /* slm heuristic bandwidth correction */
} t_ctlformant;

typedef struct formant
{
	t_pxobject x_obj;
	//t_head x_h;
	//t_sig *x_io[IN1]; 
	void *x_out[5]; 
	t_ctlformant *x_ctl;
	t_predictor *x_predictor;
	int x_vs;   // vector size
	int x_npts;
	int x_specsize;
	int x_wnum;
	int x_numinterp;
	int x_index;
	int printnext;
} t_formant;


/*Prototypes*/
void LPC (t_predictor *x,int n,int w);
void formant_bang(t_formant *x);
void formant_print(t_formant *x);
void funzero(double *f,int n);
t_int *formant_perform(t_int *w);
void formant_dsp(t_formant *x, t_signal **sp, short *count);
void formant_free(t_formant *x);
int formant_alloc(t_formant *x);
int formant_predictor_alloc(t_formant *x);
void *formant_new(long npoints,long w,long fftsize);
int funlog2(int n);
void funcopy(double *f, double *g, int n);
void formant_tick(t_formant *x);
void formant_maxfreq( t_formant *x,double f);
void formant_clear(t_formant *x);
void formant_assist(t_formant *x, void *b, long m, long a, char *s);

/*
 * LPC Algorithm (le mme que pour lpc~) 
 */
void LPC (t_predictor *x,int n,int w)
{
	double *a1, *a2, *u1, *u2, *u3, *u4, *temp;
	double  BIG_E, SUM, K, gain;	
	double *sig, *wind;
	int i,i1,j;
			
	vzero(&x->AUTO[0], w+1);
	a1 = &(x->AUTO[0]);
	a2 = &(x->AUTO[w]);
	
	if (x->window_switch)					/* apply window from table */
	{
		sig = x->inbuf_start; 
		wind = x->window;
		for(i=0;i<n;i++)
		{
			*sig = *sig * (*wind);
			sig++; wind++;
		}
	}					
	while(a1 <= a2)   						/* calculate the autocorrelations */   
	{
		double *fp1, *fp2, *fp3;
		double gomper;
		fp1 = x->inbuf_start+w-(a2-a1);
		fp2 = x->inbuf_end;
		fp3 = x->inbuf_start;
		gomper = 0;
		while(fp1 < fp2)
		{
			gomper += ((*fp1)*(*fp3));
			fp1++;
			fp3++;
		}
		*a1++ = gomper / n;
	}
	BIG_E = x->AUTO[0];
	if(! BIG_E) 
		{x->debugcount2++;
		BIG_E=0.000001;}//DIRTY HACK
	for(i=1;i<=w;i++)   					/* Durbin's recursive algorithm */
	{
		i1 = i-1;
		SUM = 0.;
#if ALPHA_MATRIX
		u1 = &(x->ALPHA[i1][1]);
		u2 = &(x->ALPHA[i1][i]);
#elif ALPHA_VECTOR
		u1 = &(x->ALPHA[i1 * s + 1]);
		u2 = &(x->ALPHA[i1 * s + i]);
#endif
		a1 = &(x->AUTO[i1]);
		while(u1 < u2)  
		{
			SUM = SUM + ((*u1)*(*a1));
			u1++;
			a1--;
		}
		K = (x->AUTO[i]-SUM)/BIG_E;
		if (K > 1. || K < -1.)
		{
			//post("reflection coefficient out of range %d %f",i,K);
			x->debugcount++;
			// return ;
			for(j=0;j<=w;j++)
					*(x->currentOutBuf+j) = 0.;
			goto out;
		}
#if ALPHA_MATRIX
		x->ALPHA[i][i] = K;
		u1 = &(x->ALPHA[i][1]);
		u2 = &(x->ALPHA[i1][1]);
		u3 = &(x->ALPHA[i1][i1]);
		u4 = &(x->ALPHA[i][i]);
#elif ALPHA_VECTOR
		x->ALPHA[i * s + i] = K;
		u1 = &(x->ALPHA[i * s + 1]);
		u2 = &(x->ALPHA[i1 * s + 1]);
		u3 = &(x->ALPHA[i1 * s + i1]);
		u4 = &(x->ALPHA[i * s + i]);
#endif
		while(u1 < u4)
		{
			*u1 = *u2 - (K*(*u3));
			u1++;
			u2++;
			u3--;
		}
		BIG_E = (1-(K*K))*BIG_E;
	
	}
	gain = x->AUTO[0];


	*x->currentOutBuf = sqrt(gain);	
	temp = x->currentOutBuf;
#if ALPHA_MATRIX
	vcopy(&(x->ALPHA[w][0])+1, x->currentOutBuf+1, w);	
#elif ALPHA_VECTOR
	vcopy(&(x->ALPHA[w * s + 0])+1, x->currentOutBuf+1, w);	
#endif
	for(i=1;i<=w;i++)
		*(x->currentOutBuf+i) = - (*(x->currentOutBuf+i)) ;
out :;
}


void formant_clear(t_formant *x)
{
	int i;
	for (i = 0; i < FORM_NUM; i++) x->x_ctl->formantout[i].p_status = 0;
}

void formant_maxfreq( t_formant *x,double f)
{
	x->x_ctl->maxfreq = f;
}


void formant_print(t_formant *x)
{
	int i,t,j;
	double reform[64],imform[64],power[64],index;
		for (i=0;i<=x->x_wnum;i++)
	{
		post("out = %f",*(x->x_predictor->currentOutBuf+i));
	}
	for (i=0;i<12;i++)
	{
		post("pow = %f",x->x_ctl->power[i]);
	}
	x->printnext = 1;
	
	for(t=0;t<64;t++)
	{
		reform[t] = 0.;
		imform[t] = 0.;
	//  doinker = &(x->x_predictor->ALPHA[w_l][1]);
		for(j=0;j<=x->x_wnum;j++)
		{
			index = 2. * PI * (double)t * (double) j / (double)64.;
			reform[t] = reform[t] + *(x->x_predictor->currentOutBuf+i) * cos((double)index);	
			imform[t] = imform[t] - *(x->x_predictor->currentOutBuf+i) * sin((double)index);
		}
		power[t] = pow(reform[t],2.)+pow(imform[t],2.);
	}
	for (i=0;i<12;i++)
	{
		post("pow = %f",power[i]);
	}

}

void formant_bang(t_formant *x)
{
	int i, n = FORM_NUM;
	t_peak *foo = x->x_ctl->formantout;
	t_atom form[RAW_FORM_NUM > 3 ? RAW_FORM_NUM : 3];
	void **op;

	for (i = 0; i < RAW_FORM_NUM; i++)
	{
		form[i].a_type = A_LONG;
		/*
		form[i].a_w.w_long = (x->x_ctl->rawformant[i] > 0 ?
			69. + 17.31234 * log(x->x_ctl->rawformant[i]*(1./440.)) : 0); */
		form[i].a_w.w_long = x->x_ctl->rawformant[i];
	}
	outlet_list(x->x_out[3], (void *)0, RAW_FORM_NUM, form);
	op  = &x->x_out[0];
	form[0].a_type = A_LONG;
	form[1].a_type = form[2].a_type =form[3].a_type = A_FLOAT;

	for (i = 0; i < n; i++, foo++)
	{
		float freq = foo->p_freq;
		float amp = foo->p_db;
		float bw = foo->p_bw;
		int valid = (foo->p_status == S_ON);
		form[0].a_w.w_long = valid;
		form[1].a_w.w_float = freq;
		form[2].a_w.w_float = amp;
		form[3].a_w.w_float = bw;
		outlet_list(*op++, (void *)0, 4, form);
	}
}


t_int *formant_perform(t_int *w)
{
 	double *coefs, *lastcoefs, *coefsp;
	double gain,index;
	float *reform,*imform;
	float slope,concav,lastslope,lastconcav;
	float dBpow,dBpow1,dBpow2;
	float para_cf,para_k,para_h;
	int m,t2;
	int i;
	int j;
	int k = 0;
	int t; 
	t_peak DERIV_FIT[10];

	t_formant *x = (t_formant *)(w[1]);
	t_float *in1 = (t_float *) (w[2]);
	t_float *out = (t_float *) (w[3]);
//	t_float *out2 = (t_float *) (w[4]);

	int n=(int) w[5];
	int n2=n;
	int w_l = x->x_wnum;

	if (x->x_obj.z_disabled)
		goto out;
		
	coefs = x->x_predictor->currentOutBuf;
	coefsp = x->x_predictor->currentOutBuf;

	lastcoefs = x->x_predictor->prevOutBuf;
	
	reform = x->x_ctl->reform;
	imform = x->x_ctl->imform;

	while (n--) 
	{		
	*x->x_predictor->inbuf_current++ = (double) *in1++ ;
		if (x->x_predictor->inbuf_current == x->x_predictor->inbuf_end)	
		{
			
			if(x->x_predictor->currentOutBuf == x->x_predictor->outbufB)
			{
				x->x_predictor->currentOutBuf = x->x_predictor->outbufA;
				x->x_predictor->prevOutBuf = x->x_predictor->outbufB;
			}
			else
			{
				x->x_predictor->currentOutBuf = x->x_predictor->outbufB;
				x->x_predictor->prevOutBuf = x->x_predictor->outbufA;
			}
			/* compute LPC : */
			LPC(x->x_predictor, x->x_npts,x->x_wnum);
			gain = x->x_predictor->AUTO[0];
			for(i=1;i<=w_l;i++)
			{
				gain = gain + x->x_predictor->ALPHA[w_l][i] * x->x_predictor->AUTO[i];
			}

	/*z = c->inbuf_start;
	zend = c->inbuf_end;
	zcnum = 0;
	while(z < zend)
	{
		if(((*z)*(*(z-1)))<=0)
		{
			zcnum = zcnum + 1;
		}
		z++;
	}*/
	/************begin formant fitting from lpc data****************/
	
	/*********draw lpc spectrum, log the bins*******************/
	/* if (x->printnext)
	{
		int xx;
		for (xx = 0; xx < w; xx += 4)
		{
			post("%f\t%f\t%f\t%f", 
			(float)ALPHA[w][xx+1],(float)ALPHA[w][xx+2],
			(float)ALPHA[w][xx+2],(float)ALPHA[w][xx+3]);
		}
	} */
#if POWER_BILBAO    /* questionable power computation : */
	re = x->x_ctl->cosboink;
	s = x->x_ctl->sinboink;
	for(t=0;t<x->x_ctl->x_specsize;t++)
	{
		reform[t] = 1.;
		imform[t] = 0.;
	doinker = &(x->x_predictor->ALPHA[w_l][1]);
	//	doinker = 	coefsp;
		j = w_l;
		while(j--)
		{
			reform[t] = reform[t] - (*doinker)*(*re++);	
			imform[t] = imform[t] + (*doinker++)*(*s++);
		}
		x->x_ctl->power[t] = (1./((pow(reform[t],2)+pow(imform[t],2))));
	}

#elif POWER_DFT	  /* home made discrete fourier transform*/
	re = x->x_ctl->cosboink;
	s = x->x_ctl->sinboink;
	for(t=0;t<x->x_ctl->x_specsize;t++)
	{
		reform[t] = 0.;
		imform[t] = 0.;
	//  doinker = &(x->x_predictor->ALPHA[w_l][1]);
	//	for(j=0;j<=w_l;j++)
		for(j=1;j<=w_l;j++)
		{
			index = 2. * PI * (double)t * (double) j / (double)x->x_ctl->x_specsize;
			reform[t] = reform[t] + coefsp[j] * cos((double)index);	
			imform[t] = imform[t] - coefsp[j] * sin((double)index);
		}
		// x->x_ctl->power[t] =  log(1./sqrt(pow(reform[t],2.)+pow(imform[t],2.)));
		x->x_ctl->power[t] = (1./(pow((reform[t] + 1.),2.)+pow(imform[t],2.)));
		// why adding 1 to real part of the fft ?
	}
#else   /* fft with zeropadded coefficients for better spectral resolution */
	for(t=0;t<=w_l;t++)
		{reform[t] = (float)coefsp[t];
		imform[t] = 0.;}		
	for(;t<x->x_specsize;t++)
		{reform[t] = 0.;
		imform[t] = 0.;}
	fft(x->x_specsize,reform,imform);
	for(t=0;t<x->x_specsize;t++)
		x->x_ctl->power[t] = (double)(1./(pow((reform[t] + 1.),2.)+pow(imform[t],2.)));
		// why adding 1 to the real part of the fft ?
	
#endif
	
/*	if (x->printnext)
	{
		int xx;
		for (xx = 0; xx < 128; xx += 4)
		{
			post("power : %f %f %f %f",
				(float)(x->x_ctl->power[xx]), 
				(float)(x->x_ctl->power[xx+1]), 
				(float)(x->x_ctl->power[xx+2]), 
				(float)(x->x_ctl->power[xx+3]));
		}
	}
*/	
	/*************find peaks by using derivative tests***********/
	
	lastslope = x->x_ctl->power[2]-x->x_ctl->power[1];
	lastconcav = x->x_ctl->power[2]-2*x->x_ctl->power[1]+x->x_ctl->power[0];
	m = 0;
	for(t=3;t<x->x_specsize/2;t++)
	{
		if (m < RAW_FORM_NUM)
		{
			float newfreq;
			slope = x->x_ctl->power[t] - x->x_ctl->power[t-1];
			concav = slope-lastslope;
			if((slope*lastslope)<0) /* la derivee change de signe */
			{	
				if(concav<0)		/* c'est un maximum */
				{
					t2 = t-2;
					dBpow = 10*log(x->x_ctl->power[t]);
					dBpow1 = 10*log(x->x_ctl->power[t-1]);
					dBpow2 = 10*log(x->x_ctl->power[t2]);	     
					
					// para_cf = t2; /* no pondŽration */
					// para_cf=t2+((-3*dBpow2+4*dBpow1-dBpow)/(-2*dBpow2+4*dBpow1-2*dBpow)); /* bilbao ponderation */
					para_cf=t2 + ((dBpow1+dBpow)/(dBpow2+dBpow1+dBpow)); /* slm ponderation */
					
					para_k = (dBpow1-dBpow2)/(2*t-3-2*para_cf);
					/* para_h = dBpow2-para_k*(t2-para_cf)*(t2-para_cf); */
					//para_h = dBpow1;
					para_h = x->x_ctl->power[t-1] * coefsp[0]; // gain correction : SLM 2003
					//DERIV_FIT[m].p_freq = newfreq = pow(2,(para_cf-x->x_ctl->x_specsize+1)/12)*(SAMPLE_RATE/2.);
					DERIV_FIT[m].p_freq = newfreq = (para_cf/x->x_specsize)*SAMPLE_RATE;
					DERIV_FIT[m].p_db= para_h;
					DERIV_FIT[m].p_bw = x->x_ctl->bwscaler/concav;
					if (para_h > MINPEAK && newfreq < x->x_ctl->maxfreq)
					{
						m++;
					}
					index = 1;
				}
			}
#if 0	
		if((concav*lastconcav)<0)  /* Point d'inflexion ??? */
			{
				t2 = t-2;
				dBpow = 10*log(x->x_ctl->power[t]);
				dBpow1 = 10*log(x->x_ctl->power[t-1]);
				dBpow2 = 10*log(x->x_ctl->power[t2]);
				if((((slope>0) && 
				((concav-lastconcav)>0)) || ((slope<0) && 
				((concav-lastconcav)<0))) && (index == 0))
				{
					// DERIV_FIT[m].p_freq = newfreq = pow(2.,(t-x->x_ctl->x_specsize_MINUS_ONE)*ONE_TWELFTH)*(SAMPLE_RATE/2.);
					DERIV_FIT[m].p_freq = newfreq = (para_cf/x->x_ctl->x_specsize)*SAMPLE_RATE;
					DERIV_FIT[m].p_db = dBpow;
					DERIV_FIT[m].p_bw = -0.05;
					if (dBpow > MINPEAK && newfreq < x->x_ctl->maxfreq)
					{
						/*if (x->printnext) post("%10.6d\t%d",
							(int)(DERIV_FIT[m].p_freq),
							(int)(DERIV_FIT[m].p_db));*/
						m++;
					}
				}
			}
#endif
			lastslope = slope;
			lastconcav = concav; 
			index = 0.;
		}
	}


/****************end formant fitter*******************************/	
	
		/* save raw LPC data -- not used in current version */
//	*(c->currentOutBuf + 60) = (double) zcnum;
//	*c->currentOutBuf = sqrt(gain);
//	funcopy(&ALPHA[w][0]+1, c->currentOutBuf+1, w);

		/* try to line up the peaks with the previous ones. */


	for (i = 0; i < m; i++) x->x_ctl->rawformant[i] = DERIV_FIT[i].p_freq;
	for (i = m; i < RAW_FORM_NUM; i++) x->x_ctl->rawformant[i] = 0;

	if (m > FORM_NUM) m = FORM_NUM;	/* drop extra formants */
	for (i = 0; i < m; i++)
	{
		t_peak *p1 = &DERIV_FIT[i];
		t_peak *p2 = x->x_ctl->formantout;
		p1->p_status = -1;
		for (j = 0; j < FORM_NUM; j++, p2++)
		{
			if (p2->p_status && p2->p_freq < p1->p_freq * 1.2 &&
				p2->p_freq > p1->p_freq * .8)
			{
				p1->p_status = j;
				break;
			}
		}
	}

		/* initialize current states to zero */
	for (i = 0; i < FORM_NUM; i++) x->x_ctl->formantout[i].p_status = 0;

		/* mark states of current formants that match a new one as ON */
	for (i = 0; i < m; i++) if (DERIV_FIT[i].p_status >= 0)
		x->x_ctl->formantout[DERIV_FIT[i].p_status].p_status = S_ON;

			/* for new formants that didn't get a match, find a free
				one and mark it "NEXTON". */
	for (i = 0, j = 0; i < m; i++)
	{
		if (DERIV_FIT[i].p_status < 0)
		{
			while (x->x_ctl->formantout[j].p_status)
			{
				if (j >= FORM_NUM)
				{
					post("bug: lpc 1");
					j = 0;
					break;
				}
				j++;
			}
			DERIV_FIT[i].p_status = j;
			x->x_ctl->formantout[j].p_status = S_NEXTON;
		}
	}
		/* copy new ones in.  Old ones that aren't copied onto are already
			marked "off".  */
	for (i = 0; i < m; i++) 
	{
		t_peak *p1 = &DERIV_FIT[i];
		t_peak *p2 = x->x_ctl->formantout + p1->p_status;
		if (p1->p_status >= 0)
		{
			p2->p_freq = p1->p_freq;
			p2->p_db = p1->p_db;
			p2->p_bw = p1->p_bw;
		}
		else post("LPC bug 2");
	}

	/* if (x->printnext)
	{
		for (i = 0; i < FORM_NUM; i++)
			if (c->formantout[i].p_status)
				post("%d ---> %8.6d %d", i, (int)c->formantout[i].p_freq, 
					c->formantout[i].p_status);
			else post("%d off", i);
	} */
	x->printnext = 0;
	// if (x->x_ctl->uzi) clock_delay(x->x_ctl->clk, 0);
	//END
			x->x_predictor->inbuf_current = x->x_predictor->inbuf_start;
			x->x_index = 0;
			break; 
		}
	}
	 while(n2--)
	 {
 		*out++ = x->x_ctl->power[k++];
 		//*out++ = *coefsp++;
	 }
	out:
	return (w+6);
}


void formant_dsp(t_formant *x, t_signal **sp, short *count)
{
	dsp_add(formant_perform, 5,x, sp[0]->s_vec, sp[1]->s_vec, 0, sp[0]->s_n);
}

void formant_tick(t_formant *x)
{
	outlet_bang(x);
}


void formant_free(t_formant *x)
{
long vect_size = x->x_vs;
short totalsize = 0;

totalsize += x->x_npts * sizeof(double);
freebytes(x->x_predictor->inbuf_start,x->x_npts * sizeof(double));
totalsize += vect_size * sizeof(double);
freebytes(x->x_predictor->outbufA,vect_size * sizeof(double));
totalsize += vect_size * sizeof(double);
freebytes(x->x_predictor->outbufB,vect_size * sizeof(double));
totalsize += x->x_npts * sizeof(double);
freebytes(x->x_predictor->window,x->x_npts * sizeof(double));
totalsize += (2 + x->x_npts) * sizeof(double);
freebytes(x->x_predictor->AUTO,(2 + x->x_npts) * sizeof(double));
#if ALPHA_VECTOR
freebytes(x->x_predictor->ALPHA, (2 + x->x_predictor->a_s) * (2 + x->x_predictor->a_s) * sizeof(double);
#endif
totalsize += sizeof (t_predictor);
freebytes(x->x_predictor, sizeof (t_predictor));

totalsize += (FORM_NUM)*sizeof(t_peak);
freebytes(x->x_ctl->formantout,(FORM_NUM)*sizeof(t_peak));
totalsize += (x->x_specsize)*sizeof(float);
freebytes(x->x_ctl->reform,(x->x_specsize)*sizeof(float));
totalsize += (x->x_specsize)*sizeof(float);
freebytes(x->x_ctl->imform,(x->x_specsize)*sizeof(float));
totalsize += (x->x_specsize)*sizeof(double);
freebytes(x->x_ctl->sinboink,(x->x_specsize)*sizeof(double));
totalsize += (x->x_specsize)*sizeof(double);
freebytes(x->x_ctl->cosboink,(x->x_specsize)*sizeof(double));
totalsize += (x->x_specsize)*sizeof(double);
freebytes(x->x_ctl->power,(x->x_specsize)*sizeof(double));
totalsize += (x->x_specsize)*sizeof(double);
freebytes(x->x_ctl->freqlog,(x->x_specsize)*sizeof(double));
totalsize += sizeof(t_ctlformant);
freebytes(x->x_ctl,sizeof(t_ctlformant));
// post ("free %d",totalsize);

dsp_free((t_pxobject *)x);
//freeobject((t_object *)x);
}

int formant_predictor_alloc(t_formant *x)
{
	double *crap;
	double pi = 4 * atan(1.);
	short size,i;
	short totalsize = 0;

    x->x_vs = VECTOR_SIZE;
    
	size = sizeof (t_predictor);
	if(!(x->x_predictor = (t_predictor *)getbytes(size)))
//    if(!(x->x_predictor = (t_predictor *)sysmem_newptr(size)))
		{post("memory allocation failed"); return 0;}
	totalsize += size;

	size = x->x_npts * sizeof(double);
	if(!(x->x_predictor->inbuf_start = (double *) getbytes(size)))
		{post("memory allocation failed"); return 0;}
	totalsize += size;
	vzero(x->x_predictor->inbuf_start, x->x_npts);
	x->x_predictor->inbuf_current = x->x_predictor->inbuf_start;
	x->x_predictor->inbuf_end = x->x_predictor->inbuf_start + x->x_npts;
    
	x->x_numinterp = x->x_npts/x->x_vs; 
    
	size = x->x_vs * sizeof(double);
	if(!(x->x_predictor->outbufA = (double *) getbytes(size))) 
		{post("outbufA memory allocation failed"); return 0;}
	totalsize += size;
	if(!(x->x_predictor->outbufB = (double *) getbytes(size)))  
		{post("outbufB memory allocation failed"); return 0;}
	totalsize += size;
	vzero(x->x_predictor->outbufA, x->x_vs);
	vzero(x->x_predictor->outbufB, x->x_vs);
	x->x_predictor->currentOutBuf = x->x_predictor->outbufA;
	x->x_predictor->prevOutBuf = x->x_predictor->outbufB;
    
//crash here    return 0;
    
	/* make window */
	size = x->x_npts * sizeof(double);
	if(!(x->x_predictor->window = (double *) getbytes(size)))
		{post("window memory allocation failed"); return 0;}
	totalsize += size;
	crap = x->x_predictor->window;
		for(i=0;i<x->x_npts;i++)      
			*crap++ = (cos(pi + pi * ((float)i / (float)(x->x_npts * 0.5))) + 1.) / 2.;
	
	/*autocorrelation matrix allocation */
	size = (2 + x->x_npts) * sizeof(double);
	if(!(x->x_predictor->AUTO = (double *)getbytes(size)))
		{post("AUTO memory allocation failed"); return 0;}
	totalsize += size;

	x->x_predictor->a_s = x->x_wnum ;//+ 1;
#if ALPHA_VECTOR
	x->x_predictor->ALPHA = (double *)NULL;
	size = (2 + x->x_predictor->a_s) * (2 + x->x_predictor->a_s) * sizeof(double);

	if(!(x->x_predictor->ALPHA = (double *)getbytes(size)))
		{post("ALPHA memory allocation failed (%d)",size);
		 return 0;}
	//	 post("alloc ALPHA %d %d",x->x_predictor->ALPHA,size);

		vzero(x->x_predictor->ALPHA, x->x_predictor->a_s * x->x_predictor->a_s);

#endif
//post("alloc %d",totalsize);
return 1;
}

int formant_alloc(t_formant *x)
{
	short size;
	short totalsize = 0;
	
	size = sizeof (t_ctlformant);
	if(!(x->x_ctl = (t_ctlformant *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;

	size = (FORM_NUM)*sizeof(t_peak);
	if(!(x->x_ctl->formantout = (t_peak *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;

	size = (x->x_specsize)*sizeof(float);
	if(!(x->x_ctl->imform = (float *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;
	if(!(x->x_ctl->reform = (float *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;
	size = (x->x_specsize)*sizeof(double);
	if(!(x->x_ctl->sinboink = (double *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;
	if(!(x->x_ctl->cosboink = (double *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;} 
	totalsize += size;
	if(!(x->x_ctl->power = (double *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;
	if(!(x->x_ctl->freqlog = (double *)getbytes(size)))
		{post("ctl memory allocation failed"); return 0;}
	totalsize += size;
//	post ("alloc %d",totalsize);
return(1);
}

void *formant_new(long npoints,long w,long specsize)
{
	t_formant *x = object_alloc(formant_class);	
	long vect_size = sys_getblksize();

	if (!npoints) npoints = 512;
	if (!(powerof2p(npoints)))
	{
		post("formant: power of two required as argument");
		return (0);
	}
	if (npoints > MAXPOINTS || npoints < MINPOINTS)
	{
		post("formant : argument out of range");
		return (0);
	}
	
		if (!specsize) specsize = 512;
		if (!(powerof2p(specsize)))
	{
		post("formant: power of two required as third argument");
		return (0);
	}
	if (specsize > MAXPOINTS || specsize < MINPOINTS)
	{
		post("formant : argument out of range");
		return (0);
	}


		if (w > WMAX || w < 1)
	{
		error("lpc : trop de poles");
		return (0);
	}

    post("vector size %d", vect_size);
 
	dsp_setup((t_pxobject *)x,1);
	x->x_out[3] = listout((t_object *)x);
	x->x_out[2] = listout((t_object *)x);
	x->x_out[1] = listout((t_object *)x);
	x->x_out[0] = listout((t_object *)x);

	outlet_new((t_object *)x,"signal");	/* 1 outlet = signal */

	x->x_vs = vect_size;
	x->x_wnum = w;
	x->x_npts = npoints;
	x->x_specsize = specsize;
	x->x_numinterp = npoints/VECTOR_SIZE; 
	x->x_index = 0;
	x->printnext = 0;

	
/* predictor memory allocation */
	if (formant_predictor_alloc(x) == 0)
		{post ("p allocation failed"); return 0;}
		x->x_predictor->window_switch = 1;


/* formant memory allocation */
	if (formant_alloc(x) == 0)
		{post ("f allocation failed"); return 0;}

	x->x_ctl->uzi = 0;
//	x->x_ctl->clk = clock_new((t_object *)x, (method)formant_bang);
	x->x_ctl->maxfreq = MAXFREQ;
	x->x_ctl->bwscaler =  - pow(2,23)/( w * specsize);

	/*********generate sines and cosines for spectrum drawing**************/
#if 0
	shit = SAMPLE_RATE/(2.*PI);
	p = x->x_ctl->freqlog;
	SIN = x->x_ctl->sinboink;
	COS = x->x_ctl->cosboink;
    for(t=0;t<x->x_ctl->x_specsize;t++)
	{
		boink = PI*pow(2., (t-x->x_ctl->x_specsize_MINUS_ONE)*ONE_TWELFTH);
		*p++ = shit*boink;
		for(j=1;j<=w;j++)
		{
			jboink = j*boink;
			*SIN++ = sin(jboink);
			*COS++ = cos(jboink);
		}
	}
#endif
	return (x);
}
#define NEWSCHOOL 1 
          
#if NEWSCHOOL
int C74_EXPORT main(void)
    {
        t_class *c;
        
        c = class_new("formant~", (method)formant_new, (method)formant_free, sizeof(t_formant), 0, A_DEFLONG, A_DEFLONG, A_DEFLONG, 0);

        
        class_addmethod(c, (method)formant_dsp, "dsp", A_CANT, 0); 	// respond to the dsp message 
        class_addmethod(c, (method)formant_bang,	"bang",		0);				// the method it uses when it gets a bang in the left inlet 
 //       class_addmethod(c, (method)formant_assist,	"assist",	A_CANT, 0);		// (optional) assistance method needs to be declared like this
        class_addmethod(c, (method)formant_print,	"print", 0);		// (optional) assistance method needs to be declared like this
        class_dspinit(c);												// must call this function for MSP object classes

        class_register(CLASS_BOX, c);
        formant_class = c;
        
        post("%s", VERSION);
        return 0;
    }
#else
/* OLD SCHOOL : */
int main(void)
{
	setup((t_messlist **)&formant_class, (method) formant_new, (method) formant_free , 
		(short)sizeof(t_formant), 0, A_DEFLONG, A_DEFLONG, A_DEFLONG, 0);
	addmess((method)formant_dsp, "dsp", A_CANT, 0);
	addmess((method)formant_print, "print", 0);
//	addmess((method)formant_debug, "debug", A_CANT, 0);
//	addmess((method)formant_free, "free", 0);
	addbang((method) formant_bang); 
	post("%s", VERSION);
    dsp_initclass();
    return (0);
	
}
#endif
          
          
void formant_assist(t_formant *x, void *b, long m, long a, char *s)
    {
 /*
  if (m == ASSIST_INLET) {
            switch (a) {	
                case 0:
                    sprintf(s,"(Signal) This + Right Inlet");
                    break;
                case 1:
                    sprintf(s,"(Signal) Left Inlet + This");
                    break;
            }
        } 
        else
            sprintf(s,"???");
  */
    }


