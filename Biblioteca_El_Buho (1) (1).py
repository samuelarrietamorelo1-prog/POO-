"""Bienvenidos a la Biblioteca El Búho: aplicación local en un solo archivo Python."""

from __future__ import annotations

import json
import math
import os
import re
import subprocess
import sys
import threading
import unicodedata
import webbrowser
from abc import ABC, abstractmethod
from datetime import date, timedelta
from functools import wraps
from pathlib import Path
from typing import Any, Callable

try:
    import flask
except ImportError:
    print("Instalando Flask para ejecutar la biblioteca...")
    subprocess.check_call([sys.executable, "-m", "pip", "install", "Flask>=3.0,<4.0"])

from flask import Flask, flash, g, redirect, render_template, request, session, url_for
from jinja2 import DictLoader
from werkzeug.security import check_password_hash, generate_password_hash




class InventarioLlenoError(Exception):
    """Se alcanza el límite permitido de libros."""


class StockInsuficienteError(Exception):
    """La cantidad solicitada supera las unidades disponibles."""


class LibroNoEncontradoError(Exception):
    """No existe el libro solicitado."""


class ClienteNoEncontradoError(Exception):
    """No existe el cliente solicitado."""


class UsuarioNoEncontradoError(Exception):
    """No existe la cuenta de biblioteca solicitada."""


class PrestamoNoEncontradoError(Exception):
    """No existe el préstamo solicitado."""


class PrestamoYaDevueltoError(Exception):
    """El préstamo ya se devolvió."""


class PrestamoNoAutorizadoError(Exception):
    """El usuario intenta gestionar el préstamo de otra cuenta."""


class DatoInvalidoError(Exception):
    """Un dato no cumple las reglas del dominio."""


class Inventario:
    """Composición de libros, clientes y ventas de la librería."""

    LIMITE_LIBROS = 15

    def __init__(
        self, libros: list[Libro] | None = None,
        clientes: list[Cliente] | None = None,
        ventas: list[Venta] | None = None,
        usuarios: list[Usuario] | None = None,
        prestamos: list[Prestamo] | None = None,
    ) -> None:
        """Inicializa las colecciones que componen el catálogo y sus préstamos."""
        self.libros = list(libros or [])
        self.clientes = list(clientes or [])
        self.ventas = list(ventas or [])
        self.usuarios = list(usuarios or [])
        self.prestamos = list(prestamos or [])
        if len(self.libros) > self.LIMITE_LIBROS:
            raise InventarioLlenoError(
                "El inventario no puede contener más de 15 libros."
            )
        if len({libro.codigo.casefold() for libro in self.libros}) != len(self.libros):
            raise DatoInvalidoError(
                "El inventario contiene códigos de libro repetidos."
            )
        documentos = {cliente.documento.casefold() for cliente in self.clientes}
        if len(documentos) != len(self.clientes):
            raise DatoInvalidoError(
                "El inventario contiene documentos de cliente repetidos."
            )
        documentos_usuarios = {
            usuario.documento.casefold() for usuario in self.usuarios
        }
        nombres_usuarios = {usuario.usuario.casefold() for usuario in self.usuarios}
        correos_usuarios = {usuario.correo.casefold() for usuario in self.usuarios}
        if any(
            len(valores) != len(self.usuarios)
            for valores in (documentos_usuarios, nombres_usuarios, correos_usuarios)
        ):
            raise DatoInvalidoError("El archivo contiene cuentas de usuario repetidas.")

    def agregar_libro(self, libro: Libro) -> None:
        """Agrega un libro si se respeta el máximo y su código es único."""

        if not isinstance(libro, Libro):
            raise DatoInvalidoError("El producto agregado debe ser un libro.")
        if len(self.libros) >= self.LIMITE_LIBROS:
            raise InventarioLlenoError("El inventario ya tiene el máximo de 15 libros.")
        if self.buscar_por_codigo(libro.codigo):
            raise DatoInvalidoError(f"Ya existe un libro con el código {libro.codigo}.")
        self.libros.append(libro)

    def eliminar_libro(self, codigo: str) -> Libro:
        """Elimina un libro sin historial de ventas asociado."""
        libro = self.buscar_por_codigo(codigo)
        if libro is None:
            raise LibroNoEncontradoError(f"No se encontró el libro {codigo}.")
        if any(venta.libro.codigo == libro.codigo for venta in self.ventas):
            raise DatoInvalidoError(
                "No se puede eliminar un libro con ventas registradas."
            )
        self.libros.remove(libro)
        return libro

    def buscar_por_titulo(self, titulo: str) -> list[Libro]:
        """Busca por título, sin distinguir mayúsculas ni tildes."""
        consulta = _normalizar(titulo)
        if not consulta:
            return list(self.libros)
        return [libro for libro in self.libros if consulta in _normalizar(libro.titulo)]

    def buscar_libros(self, consulta: str) -> list[Libro]:
        """Busca título o autor con comparación sin tildes, en O(n)."""
        texto = _normalizar(consulta)
        if not texto:
            return list(self.libros)
        return [
            libro for libro in self.libros
            if texto in _normalizar(libro.titulo) or texto in _normalizar(libro.autor)
                                                  or texto in _normalizar(libro.genero)
            
        ]

    def buscar_libros_por_año(self, año):
        """Busca libros publicados en un año específico."""
        try:
            anio = int(año)
        except (ValueError, TypeError):
            raise DatoInvalidoError("El año debe ser un número válido.")

        return [
            libro for libro in self.libros
            if getattr(libro, "año_publicacion", None) == año
        ]
        
    def buscar_por_codigo(self, codigo: str) -> Libro | None:
        """Busca por código; recorre linealmente la colección."""
        objetivo = str(codigo).strip().casefold()
        return next(
            (libro for libro in self.libros if libro.codigo.casefold() == objetivo),
            None,
        )

    def registrar_cliente(self, cliente: Cliente) -> None:
        """Registra un cliente con documento único."""

        if not isinstance(cliente, Cliente):
            raise DatoInvalidoError("El registro debe ser un cliente válido.")
        if self.buscar_cliente(cliente.documento):
            raise DatoInvalidoError("Ya existe un cliente con ese documento.")
        self.clientes.append(cliente)

    def buscar_cliente(self, documento: str) -> Cliente | None:
        """Busca cliente por documento."""
        objetivo = str(documento).strip().casefold()
        return next(
            (
                cliente for cliente in self.clientes
                if cliente.documento.casefold() == objetivo
            ),
            None,
        )

    def registrar_usuario(self, usuario: Usuario) -> None:
        """Registra una cuenta con usuario, documento y correo únicos."""

        if not isinstance(usuario, Usuario):
            raise DatoInvalidoError("La cuenta de biblioteca no es válida.")
        for existente in self.usuarios:
            if existente.documento.casefold() == usuario.documento.casefold():
                raise DatoInvalidoError("Ya existe una cuenta con ese documento.")
            if existente.usuario.casefold() == usuario.usuario.casefold():
                raise DatoInvalidoError("Ese nombre de usuario ya está ocupado.")
            if existente.correo.casefold() == usuario.correo.casefold():
                raise DatoInvalidoError("Ese correo ya está registrado.")
        self.usuarios.append(usuario)

    def buscar_usuario(self, identificador: str) -> Usuario | None:
        """Busca una cuenta por usuario, correo o documento."""
        objetivo = str(identificador).strip().casefold()
        return next(
            (
                usuario for usuario in self.usuarios
                if objetivo in {
                    usuario.usuario.casefold(),
                    usuario.correo.casefold(),
                    usuario.documento.casefold(),
                }
            ),
            None,
        )

    def registrar_prestamo(
        self, usuario: Usuario, seleccion: list[tuple[str, int]],
        fecha_limite: str, codigo: str,
    ) -> Prestamo:
        """Registra un préstamo de varios títulos y descuenta stock en bloque."""

        if not isinstance(usuario, Usuario):
            raise UsuarioNoEncontradoError("Inicia sesión con una cuenta válida.")
        usuario_registrado = self.buscar_usuario(usuario.documento)
        if usuario_registrado is None:
            raise UsuarioNoEncontradoError("No se encontró la cuenta seleccionada.")
        if not seleccion:
            raise DatoInvalidoError("Selecciona al menos un libro para el préstamo.")

        cantidades: dict[str, int] = {}
        for codigo_libro, cantidad in seleccion:
            if codigo_libro in cantidades:
                cantidades[codigo_libro] += cantidad
            else:
                cantidades[codigo_libro] = cantidad

        detalles: list[DetallePrestamo] = []
        for codigo_libro, cantidad in cantidades.items():
            libro = self.buscar_por_codigo(codigo_libro)
            if libro is None:
                raise LibroNoEncontradoError(
                    f"No se encontró el libro {codigo_libro}."
                )
            detalle = DetallePrestamo(libro, cantidad)
            if detalle.cantidad > libro.stock:
                raise StockInsuficienteError(
                    f"Solo hay {libro.stock} ejemplar(es) disponibles de «{libro.titulo}»."
                )
            detalles.append(detalle)

        if any(prestamo.codigo == codigo for prestamo in self.prestamos):
            raise DatoInvalidoError("El código del préstamo ya existe.")
        prestamo = Prestamo(codigo, usuario_registrado, detalles, fecha_limite)
        for detalle in detalles:
            detalle.libro.stock -= detalle.cantidad
        self.prestamos.append(prestamo)
        usuario_registrado.prestamos.append(prestamo)
        return prestamo

    def devolver_prestamo(self, codigo: str, documento_usuario: str) -> Prestamo:
        """Marca la devolución y repone las existencias una sola vez."""
        prestamo = next(
            (fila for fila in self.prestamos if fila.codigo.casefold() == codigo.casefold()),
            None,
        )
        if prestamo is None:
            raise PrestamoNoEncontradoError("No se encontró el préstamo.")
        if prestamo.usuario.documento.casefold() != documento_usuario.casefold():
            raise PrestamoNoAutorizadoError("Ese préstamo pertenece a otra cuenta.")
        if prestamo.fecha_devolucion:
            raise PrestamoYaDevueltoError("Este préstamo ya está marcado como devuelto.")
        prestamo.fecha_devolucion = date.today().isoformat()
        for detalle in prestamo.detalles:
            detalle.libro.stock += detalle.cantidad
        return prestamo

    def prestamos_activos(self, documento_usuario: str | None = None) -> list[Prestamo]:
        """Devuelve préstamos aún no devueltos, opcionalmente de una cuenta."""
        return [
            prestamo for prestamo in self.prestamos
            if not prestamo.fecha_devolucion
            and (
                documento_usuario is None
                or prestamo.usuario.documento.casefold() == documento_usuario.casefold()
            )
        ]

    def registrar_venta(self, venta: Venta) -> None:
        """Valida referencias y stock, registra la venta y descuenta unidades."""

        if not isinstance(venta, Venta):
            raise DatoInvalidoError("La operación debe ser una venta válida.")
        libro = self.buscar_por_codigo(venta.libro.codigo)
        cliente = self.buscar_cliente(venta.cliente.documento)
        if libro is None:
            raise LibroNoEncontradoError(
                f"No se encontró el libro {venta.libro.codigo}."
            )
        if cliente is None:
            raise ClienteNoEncontradoError(
                f"No se encontró el cliente {venta.cliente.documento}."
            )
        if not isinstance(libro, Libro) or not isinstance(cliente, Cliente):
            raise DatoInvalidoError("Las referencias de la venta no son válidas.")
        if venta.cantidad > libro.stock:
            raise StockInsuficienteError(
                f"Stock insuficiente: hay {libro.stock} unidades disponibles."
            )
        if any(guardada.codigo == venta.codigo for guardada in self.ventas):
            raise DatoInvalidoError(f"Ya existe la venta {venta.codigo}.")
        venta.libro = libro
        venta.cliente = cliente
        venta.total = round(libro.precio_final() * venta.cantidad, 2)
        libro.stock -= venta.cantidad
        self.ventas.append(venta)
        cliente.compras.append(venta)

    def ventas_totales(self) -> float:
        """Suma el valor de todas las ventas registradas."""
        return round(sum(venta.total for venta in self.ventas), 2)

    def libros_bajo_stock(self) -> list[Libro]:
        """Devuelve libros con stock de tres unidades o menos."""
        return [libro for libro in self.libros if libro.stock <= 3]

    def valor_total_inventario(self) -> float:
        """Calcula el valor de venta del stock actual."""
        return round(
            sum(libro.precio_final() * libro.stock for libro in self.libros),
            2,
        )

    def to_dict(self) -> dict[str, object]:
        """Convierte el inventario completo en datos JSON compatibles."""
        return {
            "libros": [libro.to_dict() for libro in self.libros],
            "clientes": [cliente.to_dict() for cliente in self.clientes],
            "ventas": [venta.to_dict() for venta in self.ventas],
            "usuarios": [usuario.to_dict() for usuario in self.usuarios],
            "prestamos": [prestamo.to_dict() for prestamo in self.prestamos],
        }

    @classmethod
    def from_dict(cls, datos: dict[str, object]) -> Inventario:
        """Reconstruye libros, clientes y las referencias de ventas."""

        libros = []
        for fila in datos.get("libros", []):
            if not isinstance(fila, dict):
                raise DatoInvalidoError("El archivo contiene un libro mal formado.")
            libros.append(Libro.from_dict(fila))

        clientes = []
        for fila in datos.get("clientes", []):
            if not isinstance(fila, dict):
                raise DatoInvalidoError("El archivo contiene un cliente mal formado.")
            clientes.append(Cliente.from_dict(fila))

        usuarios = []
        for fila in datos.get("usuarios", []):
            if not isinstance(fila, dict):
                raise DatoInvalidoError("El archivo contiene una cuenta mal formada.")
            usuarios.append(Usuario.from_dict(fila))

        inventario = cls(libros=libros, clientes=clientes, usuarios=usuarios)
        clientes_por_documento = {cliente.documento: cliente for cliente in clientes}
        libros_por_codigo = {libro.codigo: libro for libro in libros}
        for fila in datos.get("ventas", []):
            if not isinstance(fila, dict):
                raise DatoInvalidoError("El archivo contiene una venta mal formada.")
            try:
                venta = Venta.from_dict(
                    fila,
                    clientes_por_documento[fila["cliente_documento"]],
                    libros_por_codigo[fila["libro_codigo"]],
                )
            except KeyError as exc:
                raise DatoInvalidoError(
                    "Una venta apunta a un cliente o libro inexistente."
                ) from exc
            inventario.ventas.append(venta)
            venta.cliente.compras.append(venta)

        usuarios_por_documento = {
            usuario.documento: usuario for usuario in usuarios
        }
        for fila in datos.get("prestamos", []):
            if not isinstance(fila, dict):
                raise DatoInvalidoError("El archivo contiene un préstamo mal formado.")
            prestamo = Prestamo.from_dict(fila, usuarios_por_documento, libros_por_codigo)
            inventario.prestamos.append(prestamo)
            prestamo.usuario.prestamos.append(prestamo)
        return inventario


def _normalizar(texto: str) -> str:

    return "".join(
        caracter for caracter in unicodedata.normalize("NFD", str(texto).casefold())
        if unicodedata.category(caracter) != "Mn"
    )




def _texto_obligatorio(valor: str, campo: str) -> str:
    if not isinstance(valor, str):
        raise DatoInvalidoError(f"El campo {campo} debe ser texto.")
    valor_limpio = valor.strip()
    if not valor_limpio:
        raise DatoInvalidoError(f"El campo {campo} es obligatorio.")
    return valor_limpio


class Producto(ABC):
    """Producto abstracto con código, título, precio y stock validados."""

    def __init__(self, codigo: str, titulo: str, precio: float, stock: int) -> None:
        """Inicializa un producto pasando cada campo por su setter."""
        self.codigo = codigo
        self.titulo = titulo
        self.precio = precio
        self.stock = stock

    @property
    def codigo(self) -> str:
        """Devuelve el código único del producto."""
        return self._codigo

    @codigo.setter
    def codigo(self, valor: str) -> None:
        limpio = _texto_obligatorio(valor, "código")
        if len(limpio) > 20:
            raise DatoInvalidoError("El código no puede superar 20 caracteres.")
        self._codigo = limpio.upper()

    @property
    def titulo(self) -> str:
        """Devuelve el título del producto."""
        return self._titulo

    @titulo.setter
    def titulo(self, valor: str) -> None:
        self._titulo = _texto_obligatorio(valor, "título")

    @property
    def precio(self) -> float:
        """Devuelve el precio base del producto."""
        return self._precio

    @precio.setter
    def precio(self, valor: float) -> None:
        if isinstance(valor, bool):
            raise DatoInvalidoError("El precio debe ser un número válido.")
        try:
            precio = float(valor)
        except (TypeError, ValueError) as exc:
            raise DatoInvalidoError("El precio debe ser un número válido.") from exc
        if not math.isfinite(precio) or precio <= 0:
            raise DatoInvalidoError("El precio debe ser mayor que cero.")
        self._precio = round(precio, 2)

    @property
    def stock(self) -> int:
        """Devuelve las unidades disponibles."""
        return self._stock

    @stock.setter
    def stock(self, valor: int) -> None:
        if isinstance(valor, bool) or not str(valor).strip().isdigit():
            raise DatoInvalidoError(
                "El stock debe ser un entero mayor o igual que cero."
            )
        stock = int(valor)
        if stock < 0:
            raise DatoInvalidoError(
                "El stock debe ser un entero mayor o igual que cero."
            )
        self._stock = stock

    @abstractmethod
    def precio_final(self) -> float:
        """Calcula el precio aplicado al vender el producto."""

    @abstractmethod
    def to_dict(self) -> dict[str, Any]:
        """Convierte el producto en datos serializables."""

    @classmethod
    @abstractmethod
    def from_dict(cls, datos: dict[str, Any]) -> Producto:
        """Reconstruye un producto desde datos serializados."""

    def __str__(self) -> str:
        """Devuelve una descripción breve del producto."""
        return f"{self.codigo} · {self.titulo}"


class Libro(Producto):
    """Libro con sus datos editoriales comunes."""

    def __init__(
        self, codigo: str, titulo: str, precio: float, stock: int,
        autor: str, genero: str, editorial: str, anio: int,
    ) -> None:
        """Inicializa los datos editoriales comunes a los libros."""
        super().__init__(codigo, titulo, precio, stock)
        self.autor = autor
        self.genero = genero
        self.editorial = editorial
        self.anio = anio

    @classmethod
    def from_dict(cls, datos: dict[str, Any]) -> Libro:
        """Elige la subclase concreta indicada por el tipo serializado."""
        if datos.get("tipo") == "digital":
            return LibroDigital.from_dict(datos)
        if datos.get("tipo") == "fisico":
            return LibroFisico.from_dict(datos)
        raise DatoInvalidoError("El tipo de libro del archivo no es válido.")

    def _validar_anio(self, valor: int) -> int:
        if isinstance(valor, bool) or not str(valor).strip().isdigit():
            raise DatoInvalidoError("El año de publicación debe ser entero.")
        try:
            anio = int(valor)
        except (TypeError, ValueError) as exc:
            raise DatoInvalidoError("El año de publicación debe ser entero.") from exc
        if anio < 0 or anio > date.today().year + 1:
            raise DatoInvalidoError("El año de publicación no es válido.")
        return anio

    @property
    def autor(self) -> str:
        """Devuelve el autor del libro."""
        return self._autor

    @autor.setter
    def autor(self, valor: str) -> None:
        self._autor = _texto_obligatorio(valor, "autor")

    @property
    def genero(self) -> str:
        """Devuelve el género del libro."""
        return self._genero

    @genero.setter
    def genero(self, valor: str) -> None:
        self._genero = _texto_obligatorio(valor, "género")

    @property
    def editorial(self) -> str:
        """Devuelve la editorial del libro."""
        return self._editorial

    @editorial.setter
    def editorial(self, valor: str) -> None:
        self._editorial = _texto_obligatorio(valor, "editorial")

    @property
    def anio(self) -> int:
        """Devuelve el año de publicación."""
        return self._anio

    @anio.setter
    def anio(self, valor: int) -> None:
        self._anio = self._validar_anio(valor)

    def _datos_comunes(self) -> dict[str, Any]:
        return {
            "codigo": self.codigo,
            "titulo": self.titulo,
            "precio": self.precio,
            "stock": self.stock,
            "autor": self.autor,
            "genero": self.genero,
            "editorial": self.editorial,
            "anio": self.anio,
        }


class LibroFisico(Libro):
    """Libro impreso; no modifica el precio base al venderse."""

    def __init__(
        self, codigo: str, titulo: str, precio: float, stock: int,
        autor: str, genero: str, editorial: str, anio: int,
        peso: float, estado: str = "Nuevo",
    ) -> None:
        """Inicializa un ejemplar físico con peso y estado."""
        super().__init__(codigo, titulo, precio, stock, autor, genero, editorial, anio)
        self.peso = peso
        self.estado = estado

    @property
    def peso(self) -> float:
        """Devuelve el peso en gramos."""
        return self._peso

    @peso.setter
    def peso(self, valor: float) -> None:
        if isinstance(valor, bool):
            raise DatoInvalidoError("El peso debe ser un número positivo.")
        try:
            peso = float(valor)
        except (TypeError, ValueError) as exc:
            raise DatoInvalidoError("El peso debe ser un número positivo.") from exc
        if not math.isfinite(peso) or peso <= 0:
            raise DatoInvalidoError("El peso debe ser un número positivo.")
        self._peso = peso

    @property
    def estado(self) -> str:
        """Devuelve el estado físico del libro."""
        return self._estado

    @estado.setter
    def estado(self, valor: str) -> None:
        estado = _texto_obligatorio(valor, "estado").capitalize()
        if estado not in {"Nuevo", "Usado"}:
            raise DatoInvalidoError("El estado debe ser Nuevo o Usado.")
        self._estado = estado

    def precio_final(self) -> float:
        """Devuelve el precio sin recargo ni descuento."""
        return self.precio

    @property
    def tipo(self) -> str:
        """Devuelve la etiqueta de presentación del libro."""
        return "Físico"

    def to_dict(self) -> dict[str, Any]:
        """Serializa el libro impreso."""
        return {
            **self._datos_comunes(),
            "tipo": "fisico",
            "peso": self.peso,
            "estado": self.estado,
        }

    @classmethod
    def from_dict(cls, datos: dict[str, Any]) -> LibroFisico:
        """Reconstruye un libro impreso desde un diccionario."""
        return cls(
            datos["codigo"], datos["titulo"], datos["precio"], datos["stock"],
            datos["autor"], datos["genero"], datos["editorial"], datos["anio"],
            datos["peso"], datos.get("estado", "Nuevo"),
        )


class LibroDigital(Libro):
    """Libro descargable con un descuento del diez por ciento."""

    def __init__(
        self, codigo: str, titulo: str, precio: float, stock: int,
        autor: str, genero: str, editorial: str, anio: int, formato: str,
    ) -> None:
        """Inicializa un libro descargable con formato validado."""
        super().__init__(codigo, titulo, precio, stock, autor, genero, editorial, anio)
        self.formato = formato

    @property
    def formato(self) -> str:
        """Devuelve el formato del archivo digital."""
        return self._formato

    @formato.setter
    def formato(self, valor: str) -> None:
        formato = _texto_obligatorio(valor, "formato").upper()
        if formato not in {"PDF", "EPUB", "MOBI"}:
            raise DatoInvalidoError("El formato debe ser PDF, EPUB o MOBI.")
        self._formato = formato

    def precio_final(self) -> float:
        """Aplica el descuento digital del diez por ciento."""
        return round(self.precio * 0.90, 2)

    @property
    def tipo(self) -> str:
        """Devuelve la etiqueta de presentación del libro."""
        return "Digital"

    def to_dict(self) -> dict[str, Any]:
        """Serializa el libro digital."""
        return {**self._datos_comunes(), "tipo": "digital", "formato": self.formato}

    @classmethod
    def from_dict(cls, datos: dict[str, Any]) -> LibroDigital:
        """Reconstruye un libro digital desde un diccionario."""
        return cls(
            datos["codigo"], datos["titulo"], datos["precio"], datos["stock"],
            datos["autor"], datos["genero"], datos["editorial"], datos["anio"],
            datos["formato"],
        )


class Persona:
    """Persona con nombre, documento y correo validados."""

    def __init__(self, nombre: str, documento: str, correo: str) -> None:
        """Inicializa una persona validando los tres campos."""
        self.nombre = nombre
        self.documento = documento
        self.correo = correo

    @property
    def nombre(self) -> str:
        """Devuelve el nombre de la persona."""
        return self._nombre

    @nombre.setter
    def nombre(self, valor: str) -> None:
        self._nombre = _texto_obligatorio(valor, "nombre")

    @property
    def documento(self) -> str:
        """Devuelve el documento normalizado."""
        return self._documento

    @documento.setter
    def documento(self, valor: str) -> None:
        documento = _texto_obligatorio(valor, "documento")
        if len(documento) <6 or len(documento) > 30:
            raise DatoInvalidoError("El documento tiene entre y  30 caracteres.")
        self._documento = documento

    @property
    def correo(self) -> str:
        """Devuelve el correo electrónico."""
        return self._correo

    @correo.setter
    def correo(self, valor: str) -> None:
        correo = _texto_obligatorio(valor, "correo")
        if not re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", correo):
            raise DatoInvalidoError("El correo electrónico no tiene un formato válido.")
        self._correo = correo.lower()

    def to_dict(self) -> dict[str, Any]:
        """Serializa los datos de la persona."""
        return {
            "nombre": self.nombre,
            "documento": self.documento,
            "correo": self.correo,
        }

    @classmethod
    def from_dict(cls, datos: dict[str, Any]) -> Persona:
        """Reconstruye una persona desde un diccionario."""
        return cls(datos["nombre"], datos["documento"], datos["correo"])


class Cliente(Persona):
    """Cliente y referencias en memoria a sus ventas."""

    def __init__(
        self, nombre: str, documento: str, correo: str,
        fecha_registro: str | None = None, compras: list[Venta] | None = None,
    ) -> None:
        """Inicializa un cliente con una lista de compras vacía por defecto."""
        super().__init__(nombre, documento, correo)
        self.fecha_registro = fecha_registro or date.today().isoformat()
        self.compras = compras or []

    @property
    def fecha_registro(self) -> str:
        """Devuelve la fecha ISO de registro."""
        return self._fecha_registro

    @fecha_registro.setter
    def fecha_registro(self, valor: str) -> None:
        try:
            self._fecha_registro = date.fromisoformat(str(valor)).isoformat()
        except ValueError as exc:
            raise DatoInvalidoError("La fecha de registro no es válida.") from exc

    @property
    def compras(self) -> list[Venta]:
        """Devuelve las ventas asociadas al cliente."""
        return self._compras

    @compras.setter
    def compras(self, valor: list[Venta]) -> None:
        self._compras = list(valor)

    def total_comprado(self) -> float:
        """Suma el total histórico de las ventas del cliente."""
        return round(sum(venta.total for venta in self.compras), 2)

    def to_dict(self) -> dict[str, Any]:
        """Serializa el cliente y las referencias de sus ventas."""
        return {
            **super().to_dict(),
            "fecha_registro": self.fecha_registro,
            "ventas": [venta.codigo for venta in self.compras],
        }

    @classmethod
    def from_dict(cls, datos: dict[str, Any]) -> Cliente:
        """Reconstruye un cliente; el repositorio enlaza sus ventas después."""
        return cls(
            datos["nombre"], datos["documento"], datos["correo"],
            datos.get("fecha_registro"), [],
        )


class Usuario(Persona):
    """Miembro registrado que puede solicitar y devolver préstamos."""

    def __init__(
        self, nombre: str, documento: str, correo: str, usuario: str,
        clave_hash: str, fecha_registro: str | None = None,
        prestamos: list[Prestamo] | None = None,
    ) -> None:
        """Inicializa la cuenta con un hash de contraseña, nunca texto plano."""
        super().__init__(nombre, documento, correo)
        self.usuario = usuario
        self.clave_hash = clave_hash
        self.fecha_registro = fecha_registro or date.today().isoformat()
        self.prestamos = prestamos or []

    @property
    def usuario(self) -> str:
        """Devuelve el nombre de usuario normalizado."""
        return self._usuario

    @usuario.setter
    def usuario(self, valor: str) -> None:
        usuario = _texto_obligatorio(valor, "usuario").casefold()
        if not re.fullmatch(r"[a-z0-9_.-]{3,24}", usuario):
            raise DatoInvalidoError(
                "El usuario debe tener de 3 a 24 caracteres: letras, números, punto, guion o guion bajo."
            )
        self._usuario = usuario

    @property
    def clave_hash(self) -> str:
        """Devuelve el hash almacenado de la contraseña."""
        return self._clave_hash

    @clave_hash.setter
    def clave_hash(self, valor: str) -> None:
        self._clave_hash = _texto_obligatorio(valor, "contraseña protegida")

    @property
    def fecha_registro(self) -> str:
        """Devuelve la fecha de creación de la cuenta."""
        return self._fecha_registro

    @fecha_registro.setter
    def fecha_registro(self, valor: str) -> None:
        try:
            self._fecha_registro = date.fromisoformat(str(valor)).isoformat()
        except ValueError as exc:
            raise DatoInvalidoError("La fecha de registro no es válida.") from exc

    @property
    def prestamos(self) -> list[Prestamo]:
        """Devuelve los préstamos del usuario."""
        return self._prestamos

    @prestamos.setter
    def prestamos(self, valor: list[Prestamo]) -> None:
        self._prestamos = list(valor)

    def to_dict(self) -> dict[str, Any]:
        """Serializa la cuenta sin exponer la contraseña original."""
        return {
            **super().to_dict(),
            "usuario": self.usuario,
            "clave_hash": self.clave_hash,
            "fecha_registro": self.fecha_registro,
            "prestamos": [prestamo.codigo for prestamo in self.prestamos],
        }

    @classmethod
    def from_dict(cls, datos: dict[str, Any]) -> Usuario:
        """Reconstruye una cuenta y deja que el repositorio enlace préstamos."""
        return cls(
            datos["nombre"], datos["documento"], datos["correo"],
            datos["usuario"], datos["clave_hash"],
            datos.get("fecha_registro"), [],
        )


class DetallePrestamo:
    """Cantidad de un título incluida en un préstamo."""

    def __init__(self, libro: Libro, cantidad: int) -> None:
        """Crea una línea de préstamo con una cantidad positiva."""
        if not isinstance(libro, Libro):
            raise DatoInvalidoError("El detalle requiere un libro válido.")
        if isinstance(cantidad, bool) or not str(cantidad).isdigit() or int(cantidad) < 1:
            raise DatoInvalidoError("La cantidad debe ser un entero mayor que cero.")
        self.libro = libro
        self.cantidad = int(cantidad)

    def to_dict(self) -> dict[str, Any]:
        """Serializa la referencia al libro y su cantidad."""
        return {"libro_codigo": self.libro.codigo, "cantidad": self.cantidad}

    @classmethod
    def from_dict(
        cls, datos: dict[str, Any], libros: dict[str, Libro],
    ) -> DetallePrestamo:
        """Reconstruye una línea con el libro cargado por el repositorio."""
        try:
            libro = libros[datos["libro_codigo"]]
        except KeyError as exc:
            raise DatoInvalidoError("El préstamo apunta a un libro inexistente.") from exc
        return cls(libro, datos["cantidad"])


class Prestamo:
    """Préstamo de uno o varios títulos con fecha límite y devolución."""

    def __init__(
        self, codigo: str, usuario: Usuario, detalles: list[DetallePrestamo],
        fecha_limite: str, fecha_prestamo: str | None = None,
        fecha_devolucion: str | None = None,
    ) -> None:
        """Crea un préstamo y valida sus fechas y detalles."""
        self.codigo = _texto_obligatorio(codigo, "código de préstamo")
        if not isinstance(usuario, Usuario):
            raise DatoInvalidoError("El préstamo necesita un usuario válido.")
        if not detalles or any(
            not isinstance(detalle, DetallePrestamo) for detalle in detalles
        ):
            raise DatoInvalidoError("El préstamo debe incluir al menos un libro válido.")
        self.usuario = usuario
        self.detalles = list(detalles)
        self.fecha_prestamo = fecha_prestamo or date.today().isoformat()
        self.fecha_limite = fecha_limite
        self.fecha_devolucion = fecha_devolucion

    @property
    def fecha_prestamo(self) -> str:
        """Devuelve la fecha de inicio del préstamo."""
        return self._fecha_prestamo

    @fecha_prestamo.setter
    def fecha_prestamo(self, valor: str) -> None:
        self._fecha_prestamo = _fecha_iso(valor, "fecha del préstamo")

    @property
    def fecha_limite(self) -> str:
        """Devuelve la fecha acordada para entregar los libros."""
        return self._fecha_limite

    @fecha_limite.setter
    def fecha_limite(self, valor: str) -> None:
        fecha = _fecha_iso(valor, "fecha límite")
        if fecha <= self.fecha_prestamo:
            raise DatoInvalidoError("La fecha límite debe ser posterior al inicio del préstamo.")
        self._fecha_limite = fecha

    @property
    def fecha_devolucion(self) -> str | None:
        """Devuelve la fecha de devolución, si ya se registró."""
        return self._fecha_devolucion

    @fecha_devolucion.setter
    def fecha_devolucion(self, valor: str | None) -> None:
        self._fecha_devolucion = _fecha_iso(valor, "fecha de devolución") if valor else None

    @property
    def estado(self) -> str:
        """Calcula si el préstamo está vigente, vencido o devuelto."""
        if self.fecha_devolucion:
            return "Devuelto"
        if date.fromisoformat(self.fecha_limite) < date.today():
            return "Vencido"
        return "Vigente"

    @property
    def total_ejemplares(self) -> int:
        """Cuenta todos los ejemplares de los distintos títulos."""
        return sum(detalle.cantidad for detalle in self.detalles)

    def to_dict(self) -> dict[str, Any]:
        """Serializa el préstamo conservando sus relaciones."""
        return {
            "codigo": self.codigo,
            "usuario_documento": self.usuario.documento,
            "fecha_prestamo": self.fecha_prestamo,
            "fecha_limite": self.fecha_limite,
            "fecha_devolucion": self.fecha_devolucion,
            "detalles": [detalle.to_dict() for detalle in self.detalles],
        }

    @classmethod
    def from_dict(
        cls, datos: dict[str, Any], usuarios: dict[str, Usuario],
        libros: dict[str, Libro],
    ) -> Prestamo:
        """Reconstruye un préstamo y sus líneas enlazando objetos cargados."""
        try:
            usuario = usuarios[datos["usuario_documento"]]
        except KeyError as exc:
            raise DatoInvalidoError("El préstamo apunta a un usuario inexistente.") from exc
        detalles = [
            DetallePrestamo.from_dict(fila, libros)
            for fila in datos.get("detalles", [])
        ]
        return cls(
            datos["codigo"], usuario, detalles, datos["fecha_limite"],
            datos.get("fecha_prestamo"), datos.get("fecha_devolucion"),
        )


def _fecha_iso(valor: str, campo: str) -> str:
    """Valida y normaliza una fecha ISO."""
    try:
        return date.fromisoformat(str(valor)).isoformat()
    except ValueError as exc:
        raise DatoInvalidoError(f"La {campo} no es válida.") from exc


class Venta:
    """Venta que conserva el precio aplicado en el momento de compra."""

    def __init__(
        self, codigo: str, fecha: str, cliente: Cliente, libro: Libro,
        cantidad: int, total_guardado: float | None = None,
    ) -> None:
        """Crea una venta y fija el precio aplicado en ese momento."""
        self.codigo = _texto_obligatorio(codigo, "código de venta")
        try:
            self.fecha = date.fromisoformat(fecha).isoformat()
        except ValueError as exc:
            raise DatoInvalidoError("La fecha de venta no es válida.") from exc
        if not isinstance(cliente, Cliente) or not isinstance(libro, Libro):
            raise DatoInvalidoError("La venta necesita un cliente y un libro válidos.")
        self.cliente = cliente
        self.libro = libro
        if (
            isinstance(cantidad, bool)
            or not str(cantidad).isdigit()
            or int(cantidad) < 1
        ):
            raise DatoInvalidoError("La cantidad debe ser un entero mayor que cero.")
        self.cantidad = int(cantidad)
        base = self.libro.precio_final() * self.cantidad
        if isinstance(total_guardado, bool):
            raise DatoInvalidoError("El total de la venta no es válido.")
        try:
            total = base if total_guardado is None else float(total_guardado)
        except (TypeError, ValueError) as exc:
            raise DatoInvalidoError("El total de la venta no es válido.") from exc
        if not math.isfinite(total) or total < 0:
            raise DatoInvalidoError("El total de la venta no es válido.")
        self.total = round(total, 2)

    def to_dict(self) -> dict[str, Any]:
        """Serializa claves de relación y el total histórico."""
        return {
            "codigo": self.codigo,
            "fecha": self.fecha,
            "cliente_documento": self.cliente.documento,
            "libro_codigo": self.libro.codigo,
            "cantidad": self.cantidad,
            "total": self.total,
        }

    @classmethod
    def from_dict(
        cls, datos: dict[str, Any], cliente: Cliente, libro: Libro,
    ) -> Venta:
        """Reconstruye una venta enlazando objetos ya cargados."""
        return cls(
            datos["codigo"], datos["fecha"], cliente, libro,
            datos["cantidad"], datos.get("total"),
        )




class RepositorioJSON:
    """Lee y guarda el estado de negocio sin mezclarlo con las rutas web."""

    def __init__(self, ruta: str | Path) -> None:
        """Prepara la ruta del archivo y crea su carpeta si falta."""
        self.ruta = Path(ruta)
        self.ruta.parent.mkdir(parents=True, exist_ok=True)

    def cargar(self) -> Inventario:
        """Carga el inventario o inicializa ejemplos si el archivo no existe."""
        if not self.ruta.exists():
            inventario = self._crear_inicial()
            self.guardar(inventario)
            return inventario
        try:
            datos = json.loads(self.ruta.read_text(encoding="utf-8"))
            if not isinstance(datos, dict):
                raise DatoInvalidoError("La raíz del JSON debe ser un objeto.")
            return Inventario.from_dict(datos)
        except (json.JSONDecodeError, KeyError, TypeError) as exc:
            raise DatoInvalidoError(
                f"No se pudo leer {self.ruta.name}: el JSON está dañado o incompleto."
            ) from exc

    def guardar(self, inventario: Inventario) -> None:
        """Escribe un JSON legible y reemplaza el archivo de forma atómica."""
        temporal = self.ruta.with_suffix(self.ruta.suffix + ".tmp")
        contenido = json.dumps(inventario.to_dict(), ensure_ascii=False, indent=2)
        temporal.write_text(contenido + "\n", encoding="utf-8")
        os.replace(temporal, self.ruta)

    @staticmethod
    def _crear_inicial() -> Inventario:
        """Crea ocho libros y tres clientes de ejemplo."""
        libros = [
            LibroFisico(
                "LIB-001", "Cien años de soledad", 59000, 12,
                "Gabriel García Márquez", "Novela", "Editorial Sudamericana",
                1967, 420,
            ),
            LibroFisico(
            "LIB-002" "Memento no morir" , 43000, 3,
                "Marco Aurelio", "relatos" , "Editorial unica",
                1439 , 55,
            ),   
            
            LibroFisico(
                "LIB-002", "El principito", 39000, 7,
                "Antoine de Saint-Exupéry", "Fábula", "Salamandra", 1943, 210,
            ),
            LibroFisico(
                "LIB-003", "La ciudad y los perros", 52000, 3,
                "Mario Vargas Llosa", "Novela", "Seix Barral", 1963, 380,
            ),
            LibroFisico(
                "LIB-004", "Hábitos atómicos", 68000, 2, "James Clear",
                "Desarrollo personal", "Paidós", 2018, 510,
            ),
            LibroDigital(
                "LIB-005", "Orgullo y prejuicio", 28000, 8, "Jane Austen",
                "Romance", "T. Egerton", 1813, "EPUB",
            ),
            LibroDigital(
                "LIB-006", "El arte de la guerra", 22000, 6, "Sun Tzu",
                "Estrategia", "Varias", 500, "PDF",
            ),
            LibroFisico(
                "LIB-007", "Ficciones", 46000, 4, "Jorge Luis Borges",
                "Cuento", "Sur", 1944, 320,
            ),
            LibroDigital(
                "LIB-008", "Crónica de una muerte anunciada", 31000, 1,
                "Gabriel García Márquez", "Novela", "La Oveja Negra", 1981,
                "MOBI",
            ),
        ]
        clientes = [
            Cliente("Laura Gómez", "1020304050", "laura@example.com", "2025-02-15"),
            Cliente("Andrés Rojas", "987654321", "andres@example.com", "2025-04-03"),
            Cliente("Camila Torres", "1122334455", "camila@example.com", "2025-06-21"),
        ]
        return Inventario(libros=libros, clientes=clientes)

PLANTILLAS = {
    'base.html': r'''<!doctype html>
<html lang="es" data-bs-theme="{{ tema }}">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="theme-color" content="#f6f7fb">
  <title>{% block titulo %}{{ marca }}{% endblock %} · {{ marca }}</title>
  <link rel="stylesheet" href="{{ url_for('static', filename='tabler/css/tabler.min.css') }}">
</head>
<body class="layout-fluid">
<div class="page">
  <aside class="navbar navbar-vertical navbar-expand-lg" data-bs-theme="dark">
    <div class="container-fluid">
      <button class="navbar-toggler" type="button" data-bs-toggle="collapse" data-bs-target="#sidebar-menu" aria-controls="sidebar-menu" aria-expanded="false" aria-label="Abrir navegación"><span class="navbar-toggler-icon"></span></button>
      <h1 class="navbar-brand navbar-brand-autodark"><a href="{{ url_for('inicio') }}" class="text-decoration-none text-white"><span class="avatar avatar-sm bg-azure-lt text-azure me-2">B</span>{{ marca }}</a></h1>
      <div class="navbar-nav flex-row d-lg-none">
        <a class="nav-link" href="{{ url_for('cambiar_tema', modo='dark' if tema == 'light' else 'light') }}" title="Cambiar tema">◐</a>
      </div>
      <div class="collapse navbar-collapse" id="sidebar-menu">
        <ul class="navbar-nav pt-lg-3">
          <li class="nav-item"><a class="nav-link {% if request.endpoint == 'inicio' %}active{% endif %}" href="{{ url_for('inicio') }}"><span class="nav-link-icon d-md-none d-lg-inline-block">⌂</span><span class="nav-link-title">Inicio</span></a></li>
          <li class="nav-item"><a class="nav-link {% if request.endpoint == 'catalogo' %}active{% endif %}" href="{{ url_for('catalogo') }}"><span class="nav-link-icon d-md-none d-lg-inline-block">▤</span><span class="nav-link-title">Explorar catálogo</span></a></li>
          {% if usuario_actual %}
          <li class="nav-item"><a class="nav-link {% if request.endpoint in ['mis_prestamos', 'devolver_prestamo'] %}active{% endif %}" href="{{ url_for('mis_prestamos') }}"><span class="nav-link-icon d-md-none d-lg-inline-block">↗</span><span class="nav-link-title">Mis préstamos</span></a></li>
          {% endif %}
        </ul>
        <div class="mt-auto pb-3 pt-5">
          <div class="card card-sm bg-azure-lt border-0"><div class="card-body"><div class="text-azure fw-bold">Un libro, nuevos mundos.</div><div class="text-secondary small mt-1">Elige tus lecturas y disfruta la biblioteca.</div></div></div>
        </div>
      </div>
    </div>
  </aside>
  <div class="page-wrapper">
    <header class="navbar navbar-expand-md d-print-none">
      <div class="container-fluid">
        <div class="navbar-nav flex-row order-md-last ms-auto align-items-center">
          <a class="nav-link px-3" href="{{ url_for('cambiar_tema', modo='dark' if tema == 'light' else 'light') }}" title="Cambiar apariencia"><span class="me-1">◐</span><span class="d-none d-sm-inline">{{ 'Modo oscuro' if tema == 'light' else 'Modo claro' }}</span></a>
          {% if usuario_actual %}
          <span class="nav-link d-none d-md-inline">Hola, {{ usuario_actual.nombre.split()[0] }}</span>
          <form method="post" action="{{ url_for('cerrar_sesion') }}"><button class="btn btn-outline-secondary btn-sm">Salir</button></form>
          {% else %}
          <a class="nav-link" href="{{ url_for('iniciar_sesion') }}">Ingresar</a><a class="btn btn-primary btn-sm" href="{{ url_for('registro') }}">Crear cuenta</a>
          {% endif %}
        </div>
        <div class="navbar-nav"><span class="text-secondary small">Biblioteca · Préstamos sin pagos</span></div>
      </div>
    </header>
    <main class="page-body">
      <div class="container-fluid">
        {% with mensajes = get_flashed_messages(with_categories=true) %}
          {% if mensajes %}<div class="row row-cards mb-3">{% for categoria, mensaje in mensajes %}<div class="col-12"><div class="alert alert-important alert-{{ categoria }} alert-dismissible" role="alert"><div class="d-flex"><div><strong>{{ 'Listo' if categoria == 'success' else 'Aviso' }}.</strong> {{ mensaje }}</div></div></div></div>{% endfor %}</div>{% endif %}
        {% endwith %}
        {% block contenido %}{% endblock %}
      </div>
    </main>
    <footer class="footer footer-transparent d-print-none"><div class="container-fluid"><div class="row text-center align-items-center flex-row-reverse"><div class="col-12 col-lg-auto mt-3 mt-lg-0"><ul class="list-inline list-inline-dots mb-0"><li class="list-inline-item">Proyecto académico local</li><li class="list-inline-item">Hecho para leer más</li></ul></div></div></div></footer>
  </div>
</div>
<script src="{{ url_for('static', filename='tabler/js/tabler.min.js') }}"></script>
</body>
</html>
''',
    'catalogo.html': r'''{% extends 'base.html' %}
{% block titulo %}Catálogo{% endblock %}
{% block contenido %}
<div class="page-header d-print-none mb-4"><div class="row align-items-center"><div class="col"><div class="page-pretitle">LECTURAS PARA TODOS LOS DÍAS</div><h1 class="page-title">Explora el catálogo</h1><div class="text-secondary mt-1">Busca por título o autor y revisa la disponibilidad antes de pedir.</div></div><div class="col-auto"><span class="badge bg-green-lt text-green fs-3"><span class="status-dot status-dot-animated bg-green me-1"></span>{{ libros|selectattr('stock', 'gt', 0)|list|length }} títulos disponibles</span></div></div></div>
<div class="card mb-4"><div class="card-body"><form method="get" action="{{ url_for('catalogo') }}" class="row g-3 align-items-end"><div class="col-md-7"><label class="form-label">¿Qué quieres leer?</label><input class="form-control form-control-lg" type="search" name="q" value="{{ consulta }}" placeholder="Título o nombre del autor"></div><div class="col-md-3"><label class="form-label">Género</label><select class="form-select form-select-lg" name="genero"><option value="">Todos los géneros</option>{% for opcion in generos %}<option value="{{ opcion }}" {% if opcion == genero %}selected{% endif %}>{{ opcion }}</option>{% endfor %}</select></div><div class="col-md-2 d-grid"><button class="btn btn-primary btn-lg btn-animate-icon"><span class="icon me-2">⌕</span>Buscar</button></div></form></div></div>
<form method="post" action="{{ url_for('prestar') }}">
{% if libros %}<div class="row row-cards">{% for libro in libros %}<div class="col-md-6 col-xl-4"><div class="card card-md h-100"><div class="card-status-top bg-{{ ['azure','indigo','purple','pink','orange','teal'][loop.index0 % 6] }}"></div><div class="card-body"><div class="d-flex align-items-start"><div class="avatar avatar-xl bg-{{ ['azure','indigo','purple','pink','orange','teal'][loop.index0 % 6] }}-lt text-{{ ['azure','indigo','purple','pink','orange','teal'][loop.index0 % 6] }} me-3">{{ libro.titulo.split()|map('first')|join|upper|truncate(2, true, '') }}</div><div class="flex-fill"><div class="d-flex justify-content-between align-items-center"><span class="badge bg-secondary-lt">{{ libro.genero }}</span>{% if libro.stock > 0 %}<span class="badge bg-green-lt text-green">{{ libro.stock }} disponibles</span>{% else %}<span class="badge bg-red-lt text-red">No disponible</span>{% endif %}</div><h2 class="h2 mt-3 mb-1">{{ libro.titulo }}</h2><div class="text-secondary">{{ libro.autor }}</div></div></div><div class="row mt-3 text-secondary small"><div class="col">{{ libro.editorial }}</div><div class="col-auto">{{ libro.anio }}</div></div><div class="hr-text">DETALLES</div><div class="d-flex justify-content-between"><span class="text-secondary">Formato</span><span>{{ libro.tipo|capitalize }}</span></div><div class="d-flex justify-content-between mt-2"><span class="text-secondary">Código</span><span>{{ libro.codigo }}</span></div><div class="mt-4">{% if usuario_actual and libro.stock > 0 %}<div class="form-check"><input class="form-check-input" type="checkbox" name="libro_codigo" value="{{ libro.codigo }}" id="libro-{{ loop.index }}"><label class="form-check-label fw-bold" for="libro-{{ loop.index }}">Agregar al préstamo</label></div><div class="input-group input-group-sm mt-2"><span class="input-group-text">Cantidad</span><input class="form-control" type="number" name="cantidad_{{ libro.codigo }}" min="1" max="{{ libro.stock }}" value="1" aria-label="Cantidad de {{ libro.titulo }}"></div>{% elif not usuario_actual %}<a href="{{ url_for('iniciar_sesion') }}" class="btn btn-outline-primary w-100">Ingresar para pedir</a>{% else %}<button class="btn btn-outline-secondary w-100" disabled>Sin existencias</button>{% endif %}</div></div></div></div>{% endfor %}</div>
{% else %}<div class="empty"><div class="empty-icon">⌕</div><p class="empty-title">No encontramos ese libro</p><p class="empty-subtitle text-secondary">Prueba con otro título, autor o género.</p><a class="btn btn-primary" href="{{ url_for('catalogo') }}">Ver catálogo completo</a></div>{% endif %}
{% if usuario_actual and libros %}<div class="card mt-4"><div class="card-body"><div class="row align-items-end g-3"><div class="col-md-5"><label class="form-label">Fecha límite de devolución</label><input class="form-control form-control-lg" type="date" name="fecha_limite" min="{{ fecha_minima }}" value="{{ fecha_sugerida }}" required><div class="form-hint">Puedes escoger una fecha desde mañana.</div></div><div class="col-md-4"><div class="text-secondary small">La cantidad elegida no puede superar las existencias visibles en cada ficha. No se realizan pagos.</div></div><div class="col-md-3 d-grid"><button class="btn btn-success btn-lg">✓ Confirmar préstamo</button></div></div></div></div>{% endif %}
</form>
{% endblock %}
''',
    'error.html': r'''{% extends "base.html" %}
{% block titulo %}Aviso{% endblock %}
{% block contenido %}
<div class="page-header"><div class="page-pretitle">{{ marca }}</div><h1 class="page-title">No se pudo completar la solicitud</h1></div>
<div class="card"><div class="card-body"><p class="text-secondary">Vuelve al inicio e inténtalo de nuevo.</p><a class="btn btn-primary" href="{{ url_for('inicio') }}">Ir al inicio</a></div></div>
{% endblock %}
''',
    'ingresar.html': r'''{% extends 'base.html' %}{% block titulo %}Ingresar{% endblock %}{% block contenido %}
<div class="row justify-content-center"><div class="col-md-8 col-lg-5"><div class="text-center mb-4"><div class="avatar avatar-xl bg-azure-lt text-azure mx-auto mb-3">B</div><div class="page-pretitle">QUÉ BUENO TENERTE DE VUELTA</div><h1 class="page-title justify-content-center">Ingresa a tu biblioteca</h1><div class="text-secondary mt-2">Retoma tus lecturas y revisa tus fechas de entrega.</div></div><div class="card card-md"><div class="card-body"><form method="post" action="{{ url_for('iniciar_sesion') }}"><div class="mb-3"><label class="form-label required">Usuario, correo o documento</label><input class="form-control form-control-lg" name="identificador" autocomplete="username" required autofocus value="{{ request.form.get('identificador','') }}"></div><div class="mb-3"><label class="form-label required">Contraseña</label><input class="form-control form-control-lg" type="password" name="clave" autocomplete="current-password" required></div><div class="form-footer"><button class="btn btn-primary btn-lg w-100">Ingresar</button></div></form></div></div><div class="text-center text-secondary mt-3">¿Primera vez aquí? <a href="{{ url_for('registro') }}">Crea tu cuenta</a></div></div></div>
{% endblock %}
''',
    'inicio.html': r'''{% extends 'base.html' %}
{% block titulo %}Inicio{% endblock %}
{% block contenido %}
<div class="page-header d-print-none mb-4"><div class="row align-items-center"><div class="col"><div class="page-pretitle">{{ marca }} · BIBLIOTECA ABIERTA</div><h1 class="page-title">{% if usuario_actual %}Qué bueno verte, {{ usuario_actual.nombre.split()[0] }}{% else %}Una historia nueva te espera{% endif %}</h1><div class="text-secondary mt-1">Explora el catálogo, pide prestados tus favoritos y disfruta la lectura.</div></div><div class="col-auto"><a href="{{ url_for('catalogo') }}" class="btn btn-primary btn-lg btn-animate-icon btn-animate-icon-pulse"><span class="icon me-2">⌕</span>Explorar libros</a></div></div></div>
<div class="row row-cards mb-4">
  <div class="col-sm-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="row align-items-center"><div class="col-auto"><span class="bg-azure text-white avatar">▤</span></div><div class="col"><div class="text-secondary">Títulos en catálogo</div><div class="h1 mb-0">{{ titulos }}</div></div></div></div></div></div>
  <div class="col-sm-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="row align-items-center"><div class="col-auto"><span class="bg-green text-white avatar">✓</span></div><div class="col"><div class="text-secondary">Disponibles ahora</div><div class="h1 mb-0">{{ unidades_disponibles }} <small class="text-secondary fs-4">ejemplares</small></div></div></div></div></div></div>
  {% if usuario_actual %}<div class="col-sm-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="row align-items-center"><div class="col-auto"><span class="bg-indigo text-white avatar">↗</span></div><div class="col"><div class="text-secondary">Préstamos activos</div><div class="h1 mb-0">{{ prestamos_activos }}</div></div></div></div></div></div><div class="col-sm-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="row align-items-center"><div class="col-auto"><span class="bg-orange text-white avatar">⌛</span></div><div class="col"><div class="text-secondary">Requieren atención</div><div class="h1 mb-0">{{ prestamos_vencidos }}</div></div></div></div></div></div>{% else %}<div class="col-sm-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="row align-items-center"><div class="col-auto"><span class="bg-purple text-white avatar">♡</span></div><div class="col"><div class="text-secondary">Tu cuenta</div><div class="h2 mb-0">Gratis y local</div></div></div></div></div></div><div class="col-sm-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="row align-items-center"><div class="col-auto"><span class="bg-yellow text-white avatar">✦</span></div><div class="col"><div class="text-secondary">Préstamos</div><div class="h2 mb-0">Sin pagos</div></div></div></div></div></div>{% endif %}
</div>
<div class="row row-cards">
  <div class="col-lg-8"><div class="card"><div class="card-header"><div><h2 class="card-title">Tu próxima lectura</h2><div class="text-secondary">El catálogo se actualiza con cada préstamo y devolución.</div></div><div class="card-actions"><a href="{{ url_for('catalogo') }}" class="btn btn-outline-primary btn-animate-icon"><span class="icon me-1">→</span>Ver catálogo</a></div></div><div class="card-body"><div class="row row-cards"><div class="col-md-7"><div class="text-uppercase text-secondary small fw-bold mb-2">LEE A TU RITMO</div><h2 class="display-6">Más libros.<br>Más posibilidades.</h2><p class="text-secondary">Escoge uno o varios títulos, revisa cuántos ejemplares hay y define la fecha en que los devolverás.</p>{% if not usuario_actual %}<a href="{{ url_for('registro') }}" class="btn btn-primary btn-animate-icon"><span class="icon me-2">→</span>Crear mi cuenta</a><a href="{{ url_for('iniciar_sesion') }}" class="btn btn-link">Ya tengo cuenta</a>{% else %}<a href="{{ url_for('mis_prestamos') }}" class="btn btn-primary btn-animate-icon"><span class="icon me-2">→</span>Ver mis préstamos</a>{% endif %}</div><div class="col-md-5"><div class="card card-gradient card-gradient-animated border-0 h-100"><div class="card-body d-flex flex-column justify-content-center text-center"><div class="display-1">❝</div><div class="h2">Un libro puede abrir una puerta que aún no conoces.</div><div class="text-secondary mt-2">Elige tu siguiente aventura.</div></div></div></div></div></div></div></div>
  <div class="col-lg-4"><div class="card card-md"><div class="card-status-top bg-azure"></div><div class="card-body"><div class="subheader">PRÉSTAMO SENCILLO</div><h3 class="card-title mt-2">Así funciona</h3><div class="divide-y"><div class="py-3"><span class="badge bg-azure-lt text-azure me-2">01</span> Crea tu cuenta personal</div><div class="py-3"><span class="badge bg-green-lt text-green me-2">02</span> Selecciona libros disponibles</div><div class="py-3"><span class="badge bg-purple-lt text-purple me-2">03</span> Define cuándo devolverlos</div><div class="py-3"><span class="badge bg-orange-lt text-orange me-2">04</span> Devuélvelos desde tus préstamos</div></div></div></div></div>
  {% if usuario_actual %}<div class="col-12"><div class="card"><div class="card-header"><h2 class="card-title">Actividad reciente</h2><div class="card-actions"><a href="{{ url_for('mis_prestamos') }}">Ver historial</a></div></div><div class="card-body"><div class="row row-cards">{% for prestamo in prestamos_recientes %}<div class="col-md-6 col-xl-3"><div class="card card-sm"><div class="card-body"><div class="d-flex justify-content-between"><span class="badge bg-{{ 'green' if prestamo.estado == 'Vigente' else 'red' if prestamo.estado == 'Vencido' else 'secondary' }}-lt">{{ prestamo.estado }}</span><span class="text-secondary small">{{ prestamo.fecha_prestamo }}</span></div><div class="h3 mt-3">{{ prestamo.codigo }}</div><div class="text-secondary">{{ prestamo.total_ejemplares }} ejemplar(es) · Hasta {{ prestamo.fecha_limite }}</div></div></div></div>{% else %}<div class="col-12 text-secondary">Aún no tienes préstamos. Explora el catálogo para empezar.</div>{% endfor %}</div></div></div></div>{% endif %}
</div>
{% endblock %}
''',
    'mis_prestamos.html': r'''{% extends 'base.html' %}{% block titulo %}Mis préstamos{% endblock %}{% block contenido %}
<div class="page-header d-print-none mb-4"><div class="row align-items-center"><div class="col"><div class="page-pretitle">TU HISTORIAL DE LECTURA</div><h1 class="page-title">Mis préstamos</h1><div class="text-secondary mt-1">Controla las fechas y devuelve los ejemplares cuando termines.</div></div><div class="col-auto"><a class="btn btn-primary" href="{{ url_for('catalogo') }}">＋ Pedir libros</a></div></div></div>
{% if prestamos %}<div class="row row-cards">{% for prestamo in prestamos %}<div class="col-12"><div class="card"><div class="card-header"><div><div class="subheader">SOLICITUD {{ prestamo.codigo }}</div><h2 class="card-title">{{ prestamo.total_ejemplares }} ejemplar(es)</h2></div><div class="card-actions"><span class="badge bg-{{ 'green' if prestamo.estado == 'Vigente' else 'red' if prestamo.estado == 'Vencido' else 'secondary' }}-lt">{{ prestamo.estado }}</span></div></div><div class="card-body"><div class="row g-3"><div class="col-md-3"><div class="text-secondary small">Fecha del préstamo</div><div class="h3">{{ prestamo.fecha_prestamo }}</div></div><div class="col-md-3"><div class="text-secondary small">Devolver antes de</div><div class="h3">{{ prestamo.fecha_limite }}</div></div><div class="col-md-6"><div class="text-secondary small mb-2">Libros incluidos</div><div class="row row-cards">{% for detalle in prestamo.detalles %}<div class="col-sm-6"><div class="card card-sm"><div class="card-body"><div class="d-flex"><div class="avatar bg-azure-lt text-azure me-3">{{ detalle.libro.titulo.split()|map('first')|join|upper|truncate(2, true, '') }}</div><div><div class="fw-bold">{{ detalle.libro.titulo }}</div><div class="text-secondary small">{{ detalle.libro.autor }} · {{ detalle.cantidad }} ejemplar(es)</div></div></div></div></div></div>{% endfor %}</div></div></div></div>{% if not prestamo.fecha_devolucion %}<div class="card-footer text-end"><form method="post" action="{{ url_for('devolver_prestamo', codigo=prestamo.codigo) }}"><button class="btn btn-success">✓ Registrar devolución</button></form></div>{% else %}<div class="card-footer text-secondary">Devuelto el {{ prestamo.fecha_devolucion }}</div>{% endif %}</div></div>{% endfor %}</div>{% else %}<div class="empty"><div class="empty-icon">▤</div><p class="empty-title">Todavía no tienes préstamos</p><p class="empty-subtitle text-secondary">Explora los títulos disponibles y arma tu primera selección.</p><a class="btn btn-primary" href="{{ url_for('catalogo') }}">Explorar catálogo</a></div>{% endif %}
{% endblock %}
''',
    'registro.html': r'''{% extends 'base.html' %}{% block titulo %}Crear cuenta{% endblock %}{% block contenido %}
<div class="row justify-content-center"><div class="col-xl-9"><div class="page-header mb-4"><div class="page-pretitle">TU ESPACIO DE LECTURA</div><h1 class="page-title">Crea tu cuenta</h1><div class="text-secondary">Regístrate para pedir libros y llevar el control de tus fechas de devolución.</div></div><div class="card card-lg"><div class="row g-0"><div class="col-lg-5 d-none d-lg-flex"><div class="card-body bg-azure-lt d-flex flex-column justify-content-center"><div class="avatar avatar-xl bg-azure text-white mb-4">B</div><div class="subheader">BIBLIOTECA EL BÚHO</div><h2 class="display-6 mt-2">Tu siguiente historia empieza aquí.</h2><p class="text-secondary">Una cuenta sencilla para explorar, solicitar y devolver tus lecturas.</p><div class="badge bg-green-lt text-green w-auto">Préstamos gratuitos</div></div></div><div class="col-lg-7"><div class="card-body"><h2 class="h2 mb-4">Datos de registro</h2><form method="post" action="{{ url_for('registro') }}"><div class="mb-3"><label class="form-label required">Nombre completo</label><input class="form-control" name="nombre" autocomplete="name" required maxlength="100" value="{{ request.form.get('nombre','') }}"></div><div class="row"><div class="col-md-6 mb-3"><label class="form-label required">Documento</label><input class="form-control" name="documento" required maxlength="30" value="{{ request.form.get('documento','') }}"></div><div class="col-md-6 mb-3"><label class="form-label required">Correo electrónico</label><input class="form-control" type="email" name="correo" autocomplete="email" required maxlength="120" value="{{ request.form.get('correo','') }}"></div></div><div class="mb-3"><label class="form-label required">Nombre de usuario</label><input class="form-control" name="usuario" autocomplete="username" required minlength="3" maxlength="30" value="{{ request.form.get('usuario','') }}"><div class="form-hint">Al menos 3 caracteres.</div></div><div class="row"><div class="col-md-6 mb-3"><label class="form-label required">Contraseña</label><input class="form-control" type="password" name="clave" autocomplete="new-password" required minlength="8"></div><div class="col-md-6 mb-3"><label class="form-label required">Repetir contraseña</label><input class="form-control" type="password" name="confirmacion" autocomplete="new-password" required minlength="8"></div></div><div class="form-footer"><button class="btn btn-primary w-100">Crear mi cuenta</button></div></form><div class="text-center text-secondary mt-3">¿Ya tienes cuenta? <a href="{{ url_for('iniciar_sesion') }}">Ingresa aquí</a></div></div></div></div></div></div>
{% endblock %}
''',
}

"""Portal local de biblioteca con cuentas y préstamos en JSON."""






CARPETA = Path(__file__).resolve().parent
app = Flask(__name__)
app.jinja_loader = DictLoader(PLANTILLAS)
app.config.update(
    SECRET_KEY="biblioteca-local-clave-academica",
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
)
repositorio = RepositorioJSON(CARPETA / "datos" / "inventario.json")


def cargar_inventario() -> Inventario:
    """Carga el estado persistido de la biblioteca."""
    return repositorio.cargar()


def guardar(inventario: Inventario) -> None:
    """Guarda los cambios del catálogo o de los préstamos."""
    repositorio.guardar(inventario)


def requiere_sesion(vista: Callable[..., Any]) -> Callable[..., Any]:
    """Protege una vista para que solo la use una cuenta autenticada."""
    @wraps(vista)
    def protegida(*args: Any, **kwargs: Any) -> Any:
        if g.usuario_actual is None:
            flash("Inicia sesión para gestionar tus préstamos.", "warning")
            return redirect(url_for("iniciar_sesion"))
        return vista(*args, **kwargs)

    return protegida


@app.before_request
def cargar_usuario_actual() -> None:
    """Resuelve la cuenta de la sesión antes de ejecutar la ruta."""
    g.usuario_actual = None
    documento = session.get("documento_usuario")
    if documento:
        cuenta = cargar_inventario().buscar_usuario(documento)
        if cuenta is None:
            session.clear()
        else:
            g.usuario_actual = cuenta


@app.context_processor
def valores_globales() -> dict[str, Any]:
    """Expone marca, tema y cuenta al layout Jinja."""
    tema = request.cookies.get("tema", "light")
    if tema not in {"light", "dark"}:
        tema = "light"
    return {
        "marca": "Biblioteca El Búho",
        "tema": tema,
        "usuario_actual": getattr(g, "usuario_actual", None),
    }


@app.get("/")
def inicio() -> str:
    """Presenta el panel personal o la portada pública."""
    inventario = cargar_inventario()
    cuenta = g.usuario_actual
    prestamos = cuenta.prestamos if cuenta else []
    vigentes = [prestamo for prestamo in prestamos if not prestamo.fecha_devolucion]
    vencidos = [prestamo for prestamo in vigentes if prestamo.estado == "Vencido"]
    recientes = sorted(
        prestamos,
        key=lambda prestamo: (prestamo.fecha_prestamo, prestamo.codigo),
        reverse=True,
    )[:4]
    return render_template(
        "inicio.html",
        titulos=len(inventario.libros),
        unidades_disponibles=sum(libro.stock for libro in inventario.libros),
        titulos_disponibles=sum(libro.stock > 0 for libro in inventario.libros),
        prestamos_activos=len(vigentes),
        prestamos_vencidos=len(vencidos),
        prestamos_recientes=recientes,
    )


@app.route("/registro", methods=["GET", "POST"])
def registro() -> Any:
    """Crea una cuenta de biblioteca con contraseña cifrada."""
    if g.usuario_actual:
        return redirect(url_for("inicio"))
    if request.method == "GET":
        return render_template("registro.html")

    nombre = request.form.get("nombre", "").strip()
    documento = request.form.get("documento", "").strip()
    correo = request.form.get("correo", "").strip()
    nombre_usuario = request.form.get("usuario", "").strip()
    clave = request.form.get("clave", "")
    confirmacion = request.form.get("confirmacion", "")
    try:
        if len(clave) < 8:
            raise DatoInvalidoError("La contraseña debe tener al menos 8 caracteres.")
        if clave != confirmacion:
            raise DatoInvalidoError("Las contraseñas no coinciden.")
        cuenta = Usuario(
            nombre, documento, correo, nombre_usuario,
            generate_password_hash(clave),
        )
        inventario = cargar_inventario()
        inventario.registrar_usuario(cuenta)
        guardar(inventario)
        flash("Tu cuenta quedó creada. Ya puedes iniciar sesión.", "success")
        return redirect(url_for("iniciar_sesion"))
    except DatoInvalidoError as exc:
        flash(str(exc), "danger")
        return render_template("registro.html"), 400


@app.route("/iniciar-sesion", methods=["GET", "POST"])
def iniciar_sesion() -> Any:
    """Autentica por nombre de usuario, correo o documento."""
    if g.usuario_actual:
        return redirect(url_for("inicio"))
    if request.method == "GET":
        return render_template("ingresar.html")

    identificador = request.form.get("identificador", "").strip()
    clave = request.form.get("clave", "")
    cuenta = cargar_inventario().buscar_usuario(identificador)
    if cuenta is None or not check_password_hash(cuenta.clave_hash, clave):
        flash("No reconocí esa cuenta y contraseña.", "danger")
        return render_template("ingresar.html"), 401
    session.clear()
    session["documento_usuario"] = cuenta.documento
    flash(f"Hola, {cuenta.nombre.split()[0]}. Bienvenido a la biblioteca.", "success")
    return redirect(url_for("inicio"))


@app.post("/cerrar-sesion")
def cerrar_sesion() -> Any:
    """Cierra la sesión actual."""
    session.clear()
    flash("Has cerrado sesión.", "info")
    return redirect(url_for("inicio"))


@app.get("/tema/<modo>")
def cambiar_tema(modo: str) -> Any:
    """Guarda el tema claro u oscuro en una cookie local."""
    if modo not in {"light", "dark"}:
        flash("El tema seleccionado no es válido.", "warning")
        return redirect(url_for("inicio"))
    respuesta = redirect(url_for("inicio"))
    respuesta.set_cookie("tema", modo, max_age=60 * 60 * 24 * 365, samesite="Lax")
    return respuesta


@app.get("/catalogo")
def catalogo() -> str:
    """Muestra existencias disponibles y permite buscar títulos o autores."""
    inventario = cargar_inventario()
    consulta = request.args.get("q", "").strip()
    genero = request.args.get("genero", "").strip()
    resultados = inventario.buscar_libros(consulta)
    if genero:
        resultados = [libro for libro in resultados if libro.genero == genero]
    generos = sorted({libro.genero for libro in inventario.libros}, key=str.casefold)
    return render_template(
        "catalogo.html",
        libros=resultados,
        consulta=consulta,
        genero=genero,
        generos=generos,
        fecha_minima=(date.today() + timedelta(days=1)).isoformat(),
        fecha_sugerida=(date.today() + timedelta(days=14)).isoformat(),
    )


@app.post("/prestar")
@requiere_sesion
def prestar() -> Any:
    """Solicita uno o más títulos y descuenta las existencias en bloque."""
    inventario = cargar_inventario()
    seleccion = request.form.getlist("libro_codigo")
    fecha_limite = request.form.get("fecha_limite", "").strip()
    try:
        cantidades: list[tuple[str, int]] = []
        for codigo in seleccion:
            texto = request.form.get(f"cantidad_{codigo}", "").strip()
            if not texto.isdigit() or int(texto) < 1:
                raise DatoInvalidoError(
                    "Indica una cantidad entera positiva para cada libro seleccionado."
                )
            cantidades.append((codigo, int(texto)))

        codigo_prestamo = (
            f"PRE-{date.today():%Y%m%d}-{len(inventario.prestamos) + 1:04d}"
        )
        prestamo = inventario.registrar_prestamo(
            g.usuario_actual, cantidades, fecha_limite, codigo_prestamo,
        )
        guardar(inventario)
        flash(
            f"Préstamo {prestamo.codigo} registrado: "
            f"{prestamo.total_ejemplares} ejemplar(es), entrega hasta {prestamo.fecha_limite}.",
            "success",
        )
        return redirect(url_for("mis_prestamos"))
    except (
        DatoInvalidoError,
        LibroNoEncontradoError,
        StockInsuficienteError,
        UsuarioNoEncontradoError,
    ) as exc:
        flash(str(exc), "danger")
        return redirect(url_for("catalogo"))


@app.get("/mis-prestamos")
@requiere_sesion
def mis_prestamos() -> str:
    """Presenta préstamos vigentes, vencidos y devueltos de la cuenta."""
    inventario = cargar_inventario()
    cuenta = inventario.buscar_usuario(g.usuario_actual.documento)
    prestamos = sorted(
        cuenta.prestamos,
        key=lambda prestamo: (prestamo.fecha_prestamo, prestamo.codigo),
        reverse=True,
    )
    return render_template("mis_prestamos.html", prestamos=prestamos)


@app.post("/prestamos/<codigo>/devolver")
@requiere_sesion
def devolver_prestamo(codigo: str) -> Any:
    """Registra la devolución de los libros de un préstamo propio."""
    inventario = cargar_inventario()
    try:
        inventario.devolver_prestamo(codigo, g.usuario_actual.documento)
        guardar(inventario)
        flash("Devolución registrada. Los ejemplares vuelven a estar disponibles.", "success")
    except (
        PrestamoNoAutorizadoError,
        PrestamoNoEncontradoError,
        PrestamoYaDevueltoError,
    ) as exc:
        flash(str(exc), "danger")
    return redirect(url_for("mis_prestamos"))


@app.get("/libros")
@app.get("/inventario")
@app.get("/ventas")
def legado_catalogo() -> Any:
    """Redirige las rutas del prototipo de ventas al catálogo de biblioteca."""
    return redirect(url_for("catalogo"))


@app.get("/clientes")
def legado_clientes() -> Any:
    """Redirige el directorio anterior al registro de cuentas."""
    return redirect(url_for("registro"))


@app.errorhandler(404)
def no_encontrado(_error: Exception) -> Any:
    """Evita mostrar la página de error predeterminada de Flask."""
    flash("La página solicitada no existe.", "warning")
    return redirect(url_for("inicio"))


@app.errorhandler(500)
def error_servidor(_error: Exception) -> Any:
    """Presenta un mensaje amigable ante un error inesperado."""
    flash("Ocurrió un error inesperado. Vuelve al inicio e inténtalo otra vez.", "danger")
    return render_template("error.html"), 500


if __name__ == "__main__":
    threading.Timer(
        1.2, lambda: webbrowser.open("http://127.0.0.1:5000")
    ).start()
    app.run(host="127.0.0.1", port=5000, debug=False)
