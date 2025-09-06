#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <limits.h>

#define MAX_AIR_ROUTES 5
#define MAX_IN 256

//STRUCT
typedef struct {
    int x_dest; // riga
    int y_dest; // colonna
    int costo;
} RottaAerea;

typedef struct {
    int r, q, s; // coordinate cubiche per la distanza
    int costo_uscita_terra;
    RottaAerea rotte_aeree[MAX_AIR_ROUTES];
    int vicini[6];
    int num_rotte;
    int x; // riga
    int y; // colonna
    int num_vicini;
} Esagono;

typedef struct {
    int colonne, righe;
    Esagono** celle;
} Mappa;

typedef struct {
    int id;
    int dist;
} NodoHeap;

typedef struct {
    NodoHeap* nodo;
    int size;
    int cap;
} MinHeap;

//PROTOTIPI
static inline void conversione_assiali_cubo(int indice_colonna, int indice_riga, int* q, int* r, int* s);
static inline int controlla_limite_mappa(const Mappa* m, int x, int y);
static inline int id_lineare(const Mappa* m, int x, int y);
static inline Esagono* cella_xy(Mappa* m, int x, int y);
static inline void conversione_id_coordinate(const Mappa* m, int id, int* x, int* y);
static inline Esagono* cella_id(Mappa* m, int id);
static inline void conversione_oddr_cubiche(int x, int y, int* q, int* r, int* s);
static inline int calcola_distanza_esagono(int xa, int ya, int xb, int yb);
void assegna_vicini(Mappa* m);
Mappa* crea_mappa(int num_colonne, int num_righe);
void cancella_mappa(Mappa* map);
static inline int clampa(int v);
static int trova_indice_rotta(const Esagono* partenza, int x2, int y2);
static int costo_media_preesistenti(const Esagono* partenza);
static int ha_archi_uscita_traversabili(const Esagono* e);
int change_cost(Mappa* m, int x, int y, int v, int raggio);
int toggle_air_route(Mappa* m, int x_partenza, int y_partenza, int x_destinazione, int y_destinazione);


//fatto
static inline void conversione_oddr_cubiche(int x, int y, int* q, int* r, int* s) {
    int qx = x - ((y - (y & 1)) / 2);
    int rx = y;
    int sx = -qx - rx;
    *q = qx; *r = rx; *s = sx;
}

//fatto
static inline void conversione_assiali_cubo(int indice_colonna, int indice_riga, int* q, int* r, int* s) {
    *q = indice_riga + ((indice_colonna + (indice_colonna & 1)) / 2);
    *r = -indice_riga + ((indice_colonna - (indice_colonna & 1)) / 2);
    *s = -(*q) - (*r);
}


//fatto
static inline void conversione_id_coordinate(const Mappa* m, int id, int* x, int* y) {
    *x = id % m->colonne;
    *y = id / m->colonne;
}

//fatto
static inline Esagono* cella_id(Mappa* m, int id) {
    int x, y;
    conversione_id_coordinate(m, id, &x, &y);
    return cella_xy(m, x, y);
}

//fatto
static inline int controlla_limite_mappa(const Mappa* m, int x, int y) {
    return (x >= 0 && x < m->colonne && y >= 0 && y < m->righe);
}

//fatto
static inline int id_lineare(const Mappa* m, int x, int y) {
    return y * m->colonne + x;
}

//fatto
static inline Esagono* cella_xy(Mappa* m, int x, int y) {
    int r = m->righe - 1 - y;
    int c = x;
    return &m->celle[r][c];
}


//fatto
static inline int calcola_distanza_esagono(int xa, int ya, int xb, int yb) {
    //partenza = arrivo torna 0
    if (xa == xb && ya == yb) return 0;
    //variabili per le coordinate cubiche
    int aq, ar, as, bq, br, bs;

    conversione_oddr_cubiche(xa, ya, &aq, &ar, &as);
    conversione_oddr_cubiche(xb, yb, &bq, &br, &bs);
    int dq = abs(aq - bq), dr = abs(ar - br), ds = abs(as - bs);
    return (dq + dr + ds) / 2;
}

//calcola i vicini di tutti gli esagoni sulla mappa
//potrebbe essere più efficiente calcolare solo i vicini degli esagoni che vengono visitati man mano che li visito
//durante travel_cost (per ora funziona)
void assegna_vicini(Mappa* m) {
    //check sulla mappa
    if (!m || !m->celle) return;

    //costanti per righe e colonne
    const int C = m->colonne;
    const int R = m->righe;

    //spostamenti 
    const int spost_x_pari[6] = { +1, -1,  0, -1,  0, -1 };
    const int spost_y_pari[6] = {  0,  0, +1, +1, -1, -1 };

    const int spost_x_dispari[6]  = { +1, -1, +1,  0, +1,  0 };
    const int spost_y_dispari[6]  = {  0,  0, +1, +1, -1, -1 };

    for (int i = 0; i < R; i++) {
        for (int j = 0; j < C; j++) {
            Esagono* e = &m->celle[i][j];

            int x = j;
            int y = (R - 1) - i; //perchè le righe crescono dal basso verso l'alto

            e->num_vicini = 0;

            //controllo parità riga e colonna per decidere dove posso trovare i vicini
            const int dispari = (y & 1);
            const int* DX = dispari ? spost_x_dispari : spost_x_pari; 
            const int* DY = dispari ? spost_y_dispari : spost_y_pari;

            for (int k = 0; k < 6; ++k) {
                int x_vicino = x + DX[k];
                int y_vicino = y + DY[k];
                if (x_vicino >= 0 && x_vicino < C && y_vicino >= 0 && y_vicino < R) {
                    int id = y_vicino * C + x_vicino;
                    if (e->num_vicini < 6) {
                        e->vicini[e->num_vicini++] = id;
                    }
                }
            }
        }
    }
}

//fatto
Mappa* crea_mappa(int num_colonne, int num_righe) {
    if (num_colonne <= 0 || num_righe <= 0) {
        return NULL;
    }

    Mappa* map = malloc(sizeof(Mappa));
    if (!map) return NULL;

    map->colonne = num_colonne;
    map->righe   = num_righe;

    map->celle = (Esagono**)malloc((size_t)num_righe * sizeof(Esagono*));
    if (!map->celle) {
        free(map);
        return NULL;
    }

    //alloca
    for (int i = 0; i < num_righe; i++) {
        map->celle[i] = calloc((size_t)num_colonne, sizeof(Esagono));
        if (!map->celle[i]) {
            for (int j = 0; j < i; j++) free(map->celle[j]);
            free(map->celle);
            free(map);
            return NULL;
        }
    }

    //inizializza gli esagoni
    for (int r = 0; r < num_righe; r++) {
        for (int c = 0; c < num_colonne; c++) {
            Esagono* e = &map->celle[r][c];
            e->costo_uscita_terra = 1;
            e->num_rotte = 0;
            e->x = c;
            e->y = (num_righe - 1 - r);
            conversione_assiali_cubo(e->x, e->y, &e->q, &e->r, &e->s);
        }
    }
    return map;
}

//fatto
void cancella_mappa(Mappa* map) {
    if (!map) return;
    if (map->celle) {
        for (int i = 0; i < map->righe; ++i) {
            free(map->celle[i]);
        }
        free(map->celle);
    }
    free(map);
}

//fatto
//la traccia indica valori tra 0 e 100
static inline int clampa(int v) {
    if (v < 0) return 0;
    if (v > 100) return 100;
    return v;
}

//fatto
static int trova_indice_rotta(const Esagono* partenza, int x2, int y2) {
    for (int i = 0; i < partenza->num_rotte; i++) {
        if (partenza->rotte_aeree[i].x_dest == x2 &&
            partenza->rotte_aeree[i].y_dest == y2) {
            return i;
        }
    }
    return -1;
}

//fatto
static int costo_media_preesistenti(const Esagono* partenza) {
    int somma = partenza->costo_uscita_terra;
    for (int i = 0; i < partenza->num_rotte; i++) {
        somma += partenza->rotte_aeree[i].costo;
    }
    int denom = partenza->num_rotte + 1;
    return somma / denom;          
}

//fatto
static int ha_archi_uscita_traversabili(const Esagono* e) {
    if (e->costo_uscita_terra > 0 && e->num_vicini > 0) return 1;
    for (int i = 0; i < e->num_rotte; ++i) {
        if (e->rotte_aeree[i].costo > 0) return 1;
    }
    return 0;
}

//change cost
int change_cost(Mappa* m, int x, int y, int v, int raggio) {
    if (!m || !m->celle){
        return -1;
    }
    if (!controlla_limite_mappa(m, x, y)){
        return -1;
    }
    if (raggio <= 0){
        return -1;
    }
    if(v < -10 || v > 10){
        return -1;
    }

    for (int i = 0; i < m->righe; ++i) {
        for (int j = 0; j < m->colonne; ++j) {
            int dist = calcola_distanza_esagono(j, i, x, y);
            if (dist >= raggio) continue;

            //(raggio-distEsagoni)/reggio
            double fatt = (double)(raggio - dist) / (double)raggio;
            int delta = (int)floor((double)v * fatt);

            Esagono* e = cella_xy(m, j, i);
            e->costo_uscita_terra = clampa(e->costo_uscita_terra + delta);

            for (int i = 0; i < e->num_rotte; ++i) {
                e->rotte_aeree[i].costo =
                    clampa(e->rotte_aeree[i].costo + delta);
            }
        }
    }
    return 0;
}

//toggle air route
int toggle_air_route(Mappa* m, int x_partenza, int y_partenza, int x_destinazione, int y_destinazione) {
    if (!m || !m->celle){
       return -1; 
    } 
    if (x_partenza < 0 || x_partenza >= m->colonne || y_partenza < 0 || y_partenza >= m->righe){
       return -1; 
    } 
    if (x_destinazione < 0 || x_destinazione >= m->colonne || y_destinazione < 0 || y_destinazione >= m->righe){
       return -1; 
    } 
    if (x_partenza == x_destinazione && y_partenza == y_destinazione){
       return -1; 
    } 

    Esagono* partenza = cella_xy(m, x_partenza, y_partenza);

    //se la rotta è già presente la elimino
    int idx = trova_indice_rotta(partenza, x_destinazione, y_destinazione);
    if (idx >= 0) {
        int last = partenza->num_rotte -1;
        if (idx != last) {
            partenza->rotte_aeree[idx] = partenza->rotte_aeree[last];
        }
        if(last >= 0){
           partenza->num_rotte = last; 
        }
        else{
            partenza->num_rotte = 0;
        }
        return 0; 
    }

    //check se ho spazio tra le rotte
    if (partenza->num_rotte >= MAX_AIR_ROUTES){
       return -1; 
    } 

    //tutto ok, la aggiungo
    RottaAerea nuova;
    nuova.x_dest = x_destinazione;
    nuova.y_dest = y_destinazione;
    nuova.costo  = costo_media_preesistenti(partenza);

    partenza->rotte_aeree[partenza->num_rotte++] = nuova;
    return 0; // aggiunta
}



//heap vari per usare djksta
static void crea_heap(MinHeap* mh, int cap) {
    mh->nodo = (NodoHeap*)malloc((size_t)cap * sizeof(NodoHeap));
    mh->size = 0;
    mh->cap = cap;
}

static void cancella_heap(MinHeap* mh) {
    free(mh->nodo);
    mh->nodo = NULL;
    mh->size = mh->cap = 0;
}

static inline void scambia_nodi_heap(NodoHeap* x, NodoHeap* y) {
    NodoHeap temp = *x; 
    *x = *y; 
    *y = temp;
}

static void aggiungi_nodo_heap(MinHeap* h, int id, int dist) {

    if (h->size == h->cap) {
        if (h->cap > 0) {
            h->cap = h->cap * 2; //per evitare troppe realloc
        } else {
            h->cap = 64;
        }
        h->nodo = (NodoHeap*)realloc(h->nodo, (size_t)h->cap * sizeof(NodoHeap));
    }
    int i = h->size++; //prendo la posizione libera alla fine
    h->nodo[i].id = id; //dati
    h->nodo[i].dist = dist; //dati
    while (i > 0) {
        int p = (i - 1) / 2; //padre
        if (h->nodo[p].dist <= h->nodo[i].dist) break; //confronta le distanze padre-figlio
        scambia_nodi_heap(&h->nodo[p], &h->nodo[i]); //scambia
        i = p;
    }
}

static int heap_vuoto(const MinHeap* h) { 
    return h->size == 0; }  //1 se l'heap è vuoto 0 altrimenti

static NodoHeap estrai_nodo_minimo(MinHeap* h) {
    NodoHeap top = h->nodo[0]; //primo nodo
    h->nodo[0] = h->nodo[--h->size];
    int i = 0;
    while(1) { //ciclo while per confrontare i figli 
        int figlio_sinistro = 2 * i + 1; 
        int figlio_destro = 2 * i + 2; 
        int minore = i;
        if (figlio_sinistro < h->size && h->nodo[figlio_sinistro].dist < h->nodo[minore].dist) minore = figlio_sinistro;
        if (figlio_destro < h->size && h->nodo[figlio_destro].dist < h->nodo[minore].dist) minore = figlio_destro;
        if (minore == i) break;
        scambia_nodi_heap(&h->nodo[i], &h->nodo[minore]);
        i = minore;
    }
    return top;
}

//travel cost - algoritmo di djiksta
int travel_cost(Mappa* m, int x_partenza, int y_partenza, int x_arrivo, int y_arrivo) {
    //faccio i check sulla mappa e su partenza e arrivo per vedere che sia tutto valido
    if (!m || !m->celle) {
            return -1;
        }
    if (x_partenza < 0 || x_partenza >= m->colonne || y_partenza < 0 || y_partenza >= m->righe){
            return -1;
        }
    if (x_arrivo < 0 || x_arrivo >= m->colonne || y_arrivo < 0 || y_arrivo >= m->righe){
            return -1;
        }
    if (x_partenza == x_arrivo && y_partenza == y_arrivo){
            return 0;
        }

    //controllo se posso uscire dall'esagono di partenza
    Esagono* e = cella_xy(m, x_partenza, y_partenza);
    if (!ha_archi_uscita_traversabili(e)) {
            return -1;
    }

    //sistemo coordinate
    int id_partenza = id_lineare(m, x_partenza, y_partenza);
    int id_arrivo = id_lineare(m, x_arrivo, y_arrivo);


    const int numero_celle   = m->colonne * m->righe;
    const int DIST_MAX = INT_MAX / 4; //per simulare l'infinito uso INT_MAX/4

    int*  distanza_minima = (int*)malloc((size_t)numero_celle * sizeof(int)); //alloco spazio per dijkstra
    char* visitato  = (char*)calloc((size_t)numero_celle, 1); //flag per i visitati
    if (!distanza_minima || !visitato) { //check dell'allocazione
        free(distanza_minima); 
        free(visitato); 
        return -1; 
    }

    for (int i = 0; i < numero_celle; i++) {
        distanza_minima[i] = DIST_MAX; //all'inizio sono tutti infinito
    }
    distanza_minima[id_partenza] = 0;

    //inizializzazione min-heap
    MinHeap heap; 
    crea_heap(&heap, 0);
    aggiungi_nodo_heap(&heap, id_partenza, 0);


    while (!heap_vuoto(&heap)) {
        NodoHeap nodo_corrente = estrai_nodo_minimo(&heap); //prendo il nodo con distanza minima
        int id_nodo_corrente = nodo_corrente.id; //ne prendo l'id lineare
        if (nodo_corrente.dist != distanza_minima[id_nodo_corrente]){
            continue;
        }
        if (id_nodo_corrente == id_arrivo){
           break; 
        } 
        if (visitato[id_nodo_corrente]) {
            continue;
        };
        visitato[id_nodo_corrente] = 1; //flag per visitato

        Esagono* esagono_corrente = cella_id(m, id_nodo_corrente); 

      
        if (esagono_corrente->costo_uscita_terra > 0) { //se posso uscire via terra
            int cu = esagono_corrente->costo_uscita_terra;
            for (int i = 0; i < esagono_corrente->num_vicini; i++) { //per ogni vicino 
                int id_vicino = esagono_corrente->vicini[i]; //prendo id vicino
                int nuova_distanza = distanza_minima[id_nodo_corrente] + cu; //sommo i costi
                if (nuova_distanza < distanza_minima[id_vicino]) {
                    distanza_minima[id_vicino] = nuova_distanza; //aggiorno la distanza
                    aggiungi_nodo_heap(&heap, id_vicino, nuova_distanza); //pusho nel heap
                }
            }
        }

        for (int i = 0; i < esagono_corrente->num_rotte; i++) {
            RottaAerea* rotta = &esagono_corrente->rotte_aeree[i];
            if (rotta->costo <= 0){
                continue; // non posso uscire dall'esagono via aereo
            } 
            int id_destinazione = id_lineare(m, rotta->x_dest, rotta->y_dest);
            int nuova_distanza = distanza_minima[id_nodo_corrente] + rotta->costo;
            if (nuova_distanza < distanza_minima[id_destinazione]) {
                distanza_minima[id_destinazione] = nuova_distanza;
                aggiungi_nodo_heap(&heap, id_destinazione, nuova_distanza);
            }
        }
    }

    int result = distanza_minima[id_arrivo];
    if (result >= DIST_MAX) result = -1; //irraggiungibile

    //libero memoria
    cancella_heap(&heap);
    free(distanza_minima);
    free(visitato);
    return result;
}


//----------MAIN----------
int main(void) {
      
    char linea[MAX_IN];
    int num_righe = 0; 
    int num_colonne = 0;
    Mappa* mappa = NULL;

    while (fgets(linea, sizeof(linea), stdin)) {

        //init
        if (sscanf(linea, "init %d %d", &num_colonne, &num_righe) == 2) {
            if (mappa) {
                cancella_mappa(mappa);
                mappa = NULL;
            }
            mappa = crea_mappa(num_colonne, num_righe);
            if (mappa) {
                puts("OK");
                assegna_vicini(mappa);
            } else {
                puts("KO");
            }
            continue;
        }

        //change_cost
        {
            int x, y, raggio;
            int v;
            if (sscanf(linea, "change_cost %d %d %d %d", &x, &y, &v, &raggio) == 4) {
                if (!mappa) { 
                    puts("KO"); 
                    continue; 
                }
                int risposta_change_cost = change_cost(mappa, x, y, v, raggio);
                if(risposta_change_cost == 0){
                    puts("OK");
                }else{
                    puts("KO");
                }
                continue;
            }
        }

        //toggle_air_route
        {
            int x1, y1, x2, y2;
            if (sscanf(linea, "toggle_air_route %d %d %d %d", &x1, &y1, &x2, &y2) == 4) {
                if (!mappa) { 
                    puts("KO"); 
                    continue; 
                }
                int risposta_toggle_air_route = toggle_air_route(mappa, x1, y1, x2, y2);
                if(risposta_toggle_air_route == 0){
                    puts("OK");
                }else{
                    puts("KO");
                }
                continue;
            }
        }

        //travel_cost
        {
            int xp, yp, xd, yd;
            if (sscanf(linea, "travel_cost %d %d %d %d", &xp, &yp, &xd, &yd) == 4) {
                if (!mappa) { 
                    puts("-1"); 
                    continue; }
                int cost = travel_cost(mappa, xp, yp, xd, yd);
                printf("%d\n", cost);
                continue;
            }
        }
    }

    if (mappa) cancella_mappa(mappa);
    return 0;
}
