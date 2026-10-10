# --- Build stage ---
FROM node:22-alpine AS build
WORKDIR /app

COPY package*.json ./
RUN npm ci

COPY . .
RUN npm run build

# --- Runtime stage ---
FROM nginx:alpine AS runtime

# Backend al que nginx reenvia /api. Se sustituye en el arranque (envsubst de la imagen oficial).
ENV API_UPSTREAM=api:8080

COPY --from=build /app/dist/laf-ui/browser /usr/share/nginx/html
COPY nginx.conf.template /etc/nginx/templates/default.conf.template

EXPOSE 80
