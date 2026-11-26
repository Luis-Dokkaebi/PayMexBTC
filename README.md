# PayMexBTC

Plataforma operativa del corredor de pagos México ⇄ Hong Kong con una stablecoin (PMX, 1 PMX = 1 USD) respaldada en Bitcoin y cubierta con perpetuos inversos.

Sitio estático en `web/`: un HTML, dos hojas de estilo y un script, sin dependencias ni paso de build.

```bash
python3 -m http.server -d web 8080
```

## Vistas

| Vista | Qué hace |
| --- | --- |
| Panel | Precio del oráculo, paridad PMX, colateral frente al MCR, régimen de mercado, BTC/USD de 6 h con franja de régimen y tabla de salud de la reserva. |
| Enviar | Formulario SPEI → FPS con validación real de RFC, CLABE (dígito verificador) y FPS ID. Cotiza cada segundo y ejecuta el flujo de 7 pasos con hash encadenado por paso y comprobante JSON descargable. |
| Mercado | Libros PMX/MXN, PMX/HKD, BTC/MXN y BTC/HKD. Los pares PMX cotizan con Avellaneda-Stoikov según el inventario; las órdenes a mercado recorren el libro. |
| Reservas | Saldos por bóveda, direcciones Bech32, cobertura vigente y prueba de pasivos con árbol de Merkle de 2,048 cuentas. |
| Motores | Los cinco modelos del documento de arquitectura, cada uno con su teorema y demostración. |
| Actividad | Historial guardado en el navegador, con comprobantes y exportación JSON. |

## Motores

1. **Régimen (HMM).** Baum-Welch de 3 estados sobre retorno logarítmico y log-volumen de velas de 1 minuto; filtrado hacia adelante cada segundo. `MCR_t = Σ P(s_t = i) · MCR_i` con MCR de 115 %, 135 % y 165 %. Botón de choque de −8 % y escenario de estrés de 24 h (22 %, 35 % o 50 %).
2. **Cobertura (Itô / Merton).** Corto inverso con nocional igual al PMX en circulación. Monte Carlo de 4,000 trayectorias con difusión de saltos a 30 días, con y sin cobertura. Órdenes fraccionadas cuando el último minuto tuvo un salto mayor a 3σ.
3. **Liquidez (Kelly).** Medio Kelly multivariado entre bóveda caliente HKD, caliente MXN, margen y fría, con pisos Q99.9 de cero ruina sobre la demanda de las siguientes horas y reglas de rebalanceo deterministas.
4. **Oráculo (Bayes).** Seis fuentes combinadas en una posterior normal ponderada por profundidad, con mezcla para atípicos. Disyuntor si la desviación posterior supera 20 pb o quedan menos de 3 fuentes. Payload firmado con ECDSA P-256 (WebCrypto) y verificado en el navegador.
5. **Market making (LLN).** Cotización Avellaneda-Stoikov, convergencia de la media por operación con banda de 95 % y cota de Cantelli `P(S_n ≤ 0) ≤ σ²/(σ² + nμ²)`.

## Origen de los datos

- **Precio de BTC y tipos MXN/HKD:** agregador público (CoinGecko) al cargar y cada 2 minutos. Sin red, se usa el último valor guardado.
- **Todo lo demás se genera en el navegador:** las velas de 1 minuto entre referencias (proceso con cambio de régimen y saltos), las seis fuentes del oráculo, los libros de órdenes, la tasa de fondeo, los saldos de la bóveda, los depósitos SPEI y las liquidaciones FPS. No hay conexión con bancos, exchanges ni custodios; las claves de rastreo, referencias FPS y direcciones tienen formato válido pero no corresponden a operaciones reales.
- Los supuestos de demanda del corredor (volumen diario, tamaño medio de operación, rendimiento y riesgo de la liquidez caliente) son parámetros editables en la vista Liquidez, no métricas observadas.

## Despliegue

Producción: https://paymexbtc.vercel.app

El proyecto `paymexbtc` en Vercel está conectado a este repositorio (`Luis-Dokkaebi/PayMexBTC`), con `main` como rama de producción: cada push a `main` redepliega producción y los pushes a otras ramas generan deployments de vista previa. `vercel.json` copia `web/` a `dist/`.

## Diseño

Generado con la skill Hallmark (género atmospheric, tema Midnight con ancla cálida). Tokens en `web/tokens.css`; registro en `.hallmark/log.json`.
