// Copyright 2012 Mark Cavage, Inc.  All rights reserved.

'use strict';

var domain = require('domain');
var EventEmitter = require('events').EventEmitter;
var http = require('http');
var https = require('https');
var util = require('util');

var _ = require('lodash');
var assert = require('assert-plus');
var errors = require('restify-errors');
var mime = require('mime');
var once = require('once');
var semver = require('semver');
var spdy = require('spdy');
var uuid = require('uuid');
var vasync = require('vasync');

var dtrace = require('./dtrace');
var formatters = require('./formatters');
var shallowCopy = require('./utils').shallowCopy;
var upgrade = require('./upgrade');
var deprecationWarnings = require('./deprecationWarnings');

// Ensure these are loaded
var patchRequest = require('./request');
var patchResponse = require('./response');

var http2;

patchResponse(http.ServerResponse);
patchRequest(http.IncomingMessage);

///--- Globals

var sprintf = util.format;
var maxSatisfying = semver.maxSatisfying;
var PROXY_EVENTS = [
    'clientError',
    'close',
    'connection',
    'error',
    'listening',
    'secureConnection'
];

///--- API

/**
 * Creates a new Server.
 *
 * @public
 * @class
 * @param {Object} options  - an options object
 * @param {String} options.name - Name of the server.
 * @param {Router} options.router - Router
 * @param {Object} options.log - [bunyan](https://github.com/trentm/node-bunyan)
 * instance.
 * @param {String|Array} [options.version] - Default version(s) to use in all
 * routes.
 * @param {String[]} [options.acceptable] - List of content-types this
 * server can respond with.
 * @param {String} [options.url] - Once listen() is called, this will be filled
 * in with where the server is running.
 * @param {String|Buffer} [options.certificate] - If you want to create an HTTPS
 * server, pass in a PEM-encoded certificate and key.
 * @param {String|Buffer} [options.key] - If you want to create an HTTPS server,
 * pass in a PEM-encoded certificate and key.
 * @param {Object} [options.formatters] - Custom response formatters for
 * `res.send()`.
 * @param {Boolean} [options.handleUncaughtExceptions=false] - When true restify
 * will use a domain to catch and respond to any uncaught
 * exceptions that occur in it's handler stack.
 * [bunyan](https://github.com/trentm/node-bunyan) instance.
 * response header, default is `restify`. Pass empty string to unset the header.
 * @param {Object} [options.spdy] - Any options accepted by
 * [node-spdy](https://github.com/indutny/node-spdy).
 * @param {Object} [options.http2] - Any options accepted by
 * [http2.createSecureServer](https://nodejs.org/api/http2.html).
 * @param {Boolean} [options.handleUpgrades=false] - Hook the `upgrade` event
 * from the node HTTP server, pushing `Connection: Upgrade` requests through the
 *  regular request handling chain.
 * @param {Object} [options.httpsServerOptions] - Any options accepted by
 * [node-https Server](http://nodejs.org/api/https.html#https_https).
 * If provided the following restify server options will be ignored:
 * spdy, ca, certificate, key, passphrase, rejectUnauthorized, requestCert and
 * ciphers; however these can all be specified on httpsServerOptions.
 * @param {Boolean} [options.strictRouting=false] - If set, Restify
 * will treat "/foo" and "/foo/" as different paths.
 * @example
 * var restify = require('restify');
 * var server = restify.createServer();
 *
 * srv.listen(8080, function () {
 *   console.log('ready on %s', srv.url);
 * });
 */
function Server(options) {
    assert.object(options, 'options');
    assert.object(options.log, 'options.log');
    assert.object(options.router, 'options.router');
    assert.string(options.name, 'options.name');

    var self = this;

    EventEmitter.call(this);

    this.before = [];
    this.chain = [];
    this.log = options.log;
    this.name = options.name;
    this.handleUncaughtExceptions = options.handleUncaughtExceptions || false;
    this.router = options.router;
    this.routes = {};
    this.secure = false;
    this.socketio = options.socketio || false;
    this._once = options.strictNext === false ? once : once.strict;
    this.versions = options.versions || options.version || [];
    this._inflightRequests = 0;

    var fmt = mergeFormatters(options.formatters);
    this.acceptable = fmt.acceptable;
    this.formatters = fmt.formatters;

    // TODO: revisit, register via router public interface
    this.router._afterRoute = self._afterRoute.bind(this);

    if (options.spdy) {
        this.spdy = true;
        this.server = spdy.createServer(options.spdy);
    } else if (options.http2) {
        // http2 module is not available < v8.4.0 (only with flag <= 8.8.0)
        // load http2 module here to avoid experimental warning in other cases
        if (!http2) {
            try {
                http2 = require('http2');
                patchResponse(http2.Http2ServerResponse);
                patchRequest(http2.Http2ServerRequest);
                // eslint-disable-next-line no-empty
            } catch (err) {}
        }

        assert(
            http2,
            'http2 module is not available, ' +
                'upgrade your Node.js version to >= 8.8.0'
        );

        this.http2 = true;
        this.server = http2.createSecureServer(options.http2);
    } else if ((options.cert || options.certificate) && options.key) {
        this.ca = options.ca;
        this.certificate = options.certificate || options.cert;
        this.key = options.key;
        this.passphrase = options.passphrase || null;
        this.secure = true;

        this.server = https.createServer({
            ca: self.ca,
            cert: self.certificate,
            key: self.key,
            passphrase: self.passphrase,
            rejectUnauthorized: options.rejectUnauthorized,
            requestCert: options.requestCert,
            ciphers: options.ciphers
        });
    } else if (options.httpsServerOptions) {
        this.server = https.createServer(options.httpsServerOptions);
    } else {
        this.server = http.createServer();
    }

    this.router.on('mount', this.emit.bind(this, 'mount'));

    if (!options.handleUpgrades && PROXY_EVENTS.indexOf('upgrade') === -1) {
        PROXY_EVENTS.push('upgrade');
    }
    PROXY_EVENTS.forEach(function forEach(e) {
        self.server.on(e, self.emit.bind(self, e));
    });

    // Now the things we can't blindly proxy
    this.server.on('checkContinue', function onCheckContinue(req, res) {
        if (self.listeners('checkContinue').length > 0) {
            self.emit('checkContinue', req, res);
            return;
        }

        if (!options.noWriteContinue) {
            res.writeContinue();
        }

        self._setupRequest(req, res);
        self._handle(req, res, true);
    });

    if (options.handleUpgrades) {
        this.server.on('upgrade', function onUpgrade(req, socket, head) {
            req._upgradeRequest = true;
            var res = upgrade.createResponse(req, socket, head);
            self._setupRequest(req, res);
            self._handle(req, res);
        });
    }

    this.server.on('request', this._onRequest.bind(this));

    this.__defineGetter__('maxHeadersCount', function getMaxHeadersCount() {
        return self.server.maxHeadersCount;
    });

    this.__defineSetter__('maxHeadersCount', function setMaxHeadersCount(c) {
        self.server.maxHeadersCount = c;
        return c;
    });

    this.__defineGetter__('url', function getUrl() {
        if (self.socketPath) {
            return 'http://' + self.socketPath;
        }

        var addr = self.address();
        var str = '';

        if (self.spdy) {
            str += 'spdy://';
        } else if (self.secure) {
            str += 'https://';
        } else {
            str += 'http://';
        }

        if (addr) {
            str +=
                addr.family === 'IPv6'
                    ? '[' + addr.address + ']'
                    : addr.address;
            str += ':';
            str += addr.port;
        } else {
            str += '169.254.0.1:0000';
        }

        return str;
    });

    // print deprecation messages based on server configuration
    deprecationWarnings(self);
}
util.inherits(Server, EventEmitter);

module.exports = Server;

///--- Server lifecycle methods

// eslint-disable-next-line jsdoc/check-param-names
/**
 * Gets the server up and listening.
 * Wraps node's
 * [listen()](
 * http://nodejs.org/docs/latest/api/net.html#net_server_listen_path_callback).
 *
 * @public
 * @memberof Server
 * @instance
 * @function   listen
 * @throws   {TypeError}
 * @param    {Number} port - Port
 * @param    {Number} [host] - Host
 * @param    {Function} [callback] - optionally get notified when listening.
 * @returns  {undefined} no return value
 * @example
 * <caption>You can call like:</caption>
 * server.listen(80)
 * server.listen(80, '127.0.0.1')
 * server.listen('/tmp/server.sock')
 */
Server.prototype.listen = function listen() {
    var args = Array.prototype.slice.call(arguments);
    return this.server.listen.apply(this.server, args);
};

/**
 * Shuts down this server, and invokes callback (optionally) when done.
 * Wraps node's
 * [close()](http://nodejs.org/docs/latest/api/net.html#net_event_close).
 *
 * @public
 * @memberof Server
 * @instance
 * @function   close
 * @param    {Function}  [callback] - callback to invoke when done
 * @returns  {undefined} no return value
 */
Server.prototype.close = function close(callback) {
    if (callback) {
        assert.func(callback, 'callback');
    }

    this.server.once('close', function onClose() {
        return callback ? callback() : false;
    });

    return this.server.close();
};

///--- Routing methods

/**
 * Server method opts
 * @typedef  {String|Regexp |Object} Server~methodOpts
 * @type     {Object}
 * @property {String} name a name for the route
 * @property {String|Regexp} path a string or regex matching the route
 * @property {String|String[]} version versions supported by this route
 * @example
 * // a static route
 * server.get('/foo', function(req, res, next) {});
 * // a parameterized route
 * server.get('/foo/:bar', function(req, res, next) {});
 * // a regular expression
 * server.get(/^\/([a-zA-Z0-9_\.~-]+)\/(.*)/, function(req, res, next) {});
 * // an options object
 * server.get({
 *     path: '/foo',
 *     version: ['1.0.0', '2.0.0']
 * }, function(req, res, next) {});
 */

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function get
 * @param   {Server~methodOpts} opts - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 * @example
 * server.get('/', function (req, res, next) {
 *    res.send({ hello: 'world' });
 *    next();
 * });
 */
Server.prototype.get = serverMethodFactory('GET');

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function head
 * @param   {Server~methodOpts} opts - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 */
Server.prototype.head = serverMethodFactory('HEAD');

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function post
 * @param   {Server~methodOpts} post - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 */
Server.prototype.post = serverMethodFactory('POST');

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function put
 * @param   {Server~methodOpts} put - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 */
Server.prototype.put = serverMethodFactory('PUT');

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function patch
 * @param   {Server~methodOpts} patch - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 */
Server.prototype.patch = serverMethodFactory('PATCH');

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function del
 * @param   {Server~methodOpts} opts - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 */
Server.prototype.del = serverMethodFactory('DELETE');

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @public
 * @memberof Server
 * @instance
 * @function opts
 * @param   {Server~methodOpts} opts - if string, the URL to handle.
 *                                 if options, the URL to handle, at minimum.
 * @returns {Route}                the newly created route.
 */
Server.prototype.opts = serverMethodFactory('OPTIONS');

///---  Request lifecycle and middleware methods

// eslint-disable-next-line jsdoc/check-param-names
/**
 * Gives you hooks to run _before_ any routes are located.  This gives you
 * a chance to intercept the request and change headers, etc., that routing
 * depends on.  Note that req.params will _not_ be set yet.
 *
 * @public
 * @memberof Server
 * @instance
 * @function pre
 * @param {...Function|Array} handler - Allows you to add handlers that
 * run for all routes. *before* routing occurs.
 * This gives you a hook to change request headers and the like if you need to.
 * Note that `req.params` will be undefined, as that's filled in *after*
 * routing.
 * Takes a function, or an array of functions.
 * variable number of nested arrays of handler functions
 * @returns {Object} returns self
 * @example
 * server.pre(function(req, res, next) {
 *   req.headers.accept = 'application/json';
 *   return next();
 * });
 * @example
 * <caption>For example, `pre()` can be used to deduplicate slashes in
 * URLs</caption>
 * server.pre(restify.pre.dedupeSlashes());
 */
Server.prototype.pre = function pre() {
    var self = this;
    var handlers = Array.prototype.slice.call(arguments);

    argumentsToChain(handlers).forEach(function forEach(h) {
        self.before.push(h);
    });

    return this;
};

// eslint-disable-next-line jsdoc/check-param-names
/**
 * Allows you to add in handlers that run for all routes. Note that handlers
 * added
 * via `use()` will run only after the router has found a matching route. If no
 * match is found, these handlers will never run. Takes a function, or an array
 * of functions.
 *
 * You can pass in any combination of functions or array of functions.
 *
 * @public
 * @memberof Server
 * @instance
 * @function use
 * @param {...Function|Array} handler - A variable number of handler functions
 * * and/or a
 * variable number of nested arrays of handler functions
 * @returns {Object} returns self
 */
Server.prototype.use = function use() {
    var self = this;
    var handlers = Array.prototype.slice.call(arguments);

    argumentsToChain(handlers).forEach(function forEach(h) {
        self.chain.push(h);
    });

    return this;
};

/**
 * Minimal port of the functionality offered by Express.js Route Param
 * Pre-conditions
 *
 * This basically piggy-backs on the `server.use` method. It attaches a
 * new middleware function that only fires if the specified parameter exists
 * in req.params
 *
 * Exposes an API:
 *   server.param("user", function (req, res, next) {
 *     // load the user's information here, always making sure to call next()
 *   });
 *
 * @see http://expressjs.com/guide.html#route-param%20pre-conditions
 * @public
 * @memberof Server
 * @instance
 * @function param
 * @param    {String}   name - The name of the URL param to respond to
 * @param    {Function} fn -   The middleware function to execute
 * @returns  {Object}        returns self
 */
Server.prototype.param = function param(name, fn) {
    this.use(function _param(req, res, next) {
        if (req.params && req.params[name]) {
            fn.call(this, req, res, next, req.params[name], name);
        } else {
            next();
        }
    });

    return this;
};

/**
 * Piggy-backs on the `server.use` method. It attaches a new middleware
 * function that only fires if the specified version matches the request.
 *
 * Note that if the client does not request a specific version, the middleware
 * function always fires. If you don't want this set a default version with a
 * pre handler on requests where the client omits one.
 *
 * Exposes an API:
 *   server.versionedUse("version", function (req, res, next, ver) {
 *     // do stuff that only applies to routes of this API version
 *   });
 *
 * @public
 * @memberof Server
 * @instance
 * @function versionedUse
 * @param    {String|Array} versions - the version(s) the URL to respond to
 * @param    {Function}     fn -       the middleware function to execute, the
 *                                   fourth parameter will be the selected
 *                                   version
 * @returns  {undefined} no return value
 */
Server.prototype.versionedUse = function versionedUse(versions, fn) {
    if (!Array.isArray(versions)) {
        versions = [versions];
    }
    assert.arrayOfString(versions, 'versions');

    versions.forEach(function forEach(v) {
        if (!semver.valid(v)) {
            throw new TypeError('%s is not a valid semver', v);
        }
    });

    this.use(function _versionedUse(req, res, next) {
        var ver;

        if (
            req.version() === '*' ||
            (ver = maxSatisfying(versions, req.version()) || false)
        ) {
            fn.call(this, req, res, next, ver);
        } else {
            next();
        }
    });

    return this;
};

/**
 * Removes a route from the server.
 * You pass in the route 'blob' you got from a mount call.
 *
 * @public
 * @memberof Server
 * @instance
 * @function rm
 * @throws   {TypeError} on bad input.
 * @param    {String}    route - the route name.
 * @returns  {Boolean}   true if route was removed, false if not.
 */
Server.prototype.rm = function rm(route) {
    var r = this.router.unmount(route);

    if (r && this.routes[r]) {
        delete this.routes[r];
    }

    return r;
};

///--- Info and debug methods

/**
 * Returns the server address.
 * Wraps node's
 * [address()](http://nodejs.org/docs/latest/api/net.html#net_server_address).
 *
 * @public
 * @memberof Server
 * @instance
 * @function address
 * @returns  {Object} Address of server
 * @example
 * server.address()
 * @example
 * <caption>Output:</caption>
 * { address: '::', family: 'IPv6', port: 8080 }
 */
Server.prototype.address = function address() {
    return this.server.address();
};

/**
 * Returns the number of inflight requests currently being handled by the server
 *
 * @public
 * @memberof Server
 * @instance
 * @function inflightRequests
 * @returns  {number} number of inflight requests
 */
Server.prototype.inflightRequests = function inflightRequests() {
    var self = this;
    return self._inflightRequests;
};

/**
 * Return debug information about the server.
 *
 * @public
 * @memberof Server
 * @instance
 * @function debugInfo
 * @returns {Object} debug info
 * @example
 * server.getDebugInfo()
 * @example
 * <caption>Output:</caption>
 * {
 *   routes: [
 *     {
 *       name: 'get',
 *       method: 'get',
 *       input: '/',
 *       compiledRegex: /^[\/]*$/,
 *       compiledUrlParams: null,
 *       versions: null,
 *       handlers: [Array]
 *      }
 *   ],
 *   server: {
 *     formatters: {
 *       'application/javascript': [Function: formatJSONP],
 *       'application/json': [Function: formatJSON],
 *       'text/plain': [Function: formatText],
 *       'application/octet-stream': [Function: formatBinary]
 *     },
 *     address: '::',
 *     port: 8080,
 *     inflightRequests: 0,
 *     pre: [],
 *     use: [ 'parseQueryString', '_jsonp' ],
 *     after: []
 *   }
 * }
 */
Server.prototype.getDebugInfo = function getDebugInfo() {
    var self = this;

    // map an array of function to an array of function names
    var funcNameMapper = function funcNameMapper(handler) {
        if (handler.name === '') {
            return 'anonymous';
        } else {
            return handler.name;
        }
    };

    if (!self._debugInfo) {
        var addressInfo = self.server.address();

        // output the actual routes registered with restify
        var routeInfo = self.router.getDebugInfo();
        // get each route's handler chain
        _.forEach(routeInfo, function forEach(value, key) {
            var routeName = value.name;
            value.handlers = self.routes[routeName].map(funcNameMapper);
        });

        self._debugInfo = {
            routes: routeInfo,
            server: {
                formatters: self.formatters,
                // if server is not yet listening, addressInfo may be null
                address: addressInfo && addressInfo.address,
                port: addressInfo && addressInfo.port,
                inflightRequests: self.inflightRequests(),
                pre: self.before.map(funcNameMapper),
                use: self.chain.map(funcNameMapper),
                after: self.listeners('after').map(funcNameMapper)
            }
        };
    }

    return self._debugInfo;
};

/**
 * toString() the server for easy reading/output.
 *
 * @public
 * @memberof Server
 * @instance
 * @function toString
 * @returns  {String} stringified server
 * @example
 * server.toString()
 * @example
 * <caption>Output:</caption>
 *	Accepts: application/json, text/plain, application/octet-stream,
 * application/javascript
 *	Name: restify
 *	Pre: []
 *	Router: RestifyRouter:
 *		DELETE: []
 *		GET: [get]
 *		HEAD: []
 *		OPTIONS: []
 *		PATCH: []
 *		POST: []
 *		PUT: []
 *
 *	Routes:
 *		get: [parseQueryString, _jsonp, function]
 *	Secure: false
 *	Url: http://[::]:8080
 *	Version:
 */
Server.prototype.toString = function toString() {
    var LINE_FMT = '\t%s: %s\n';
    var SUB_LINE_FMT = '\t\t%s: %s\n';
    var self = this;
    var str = '';

    function handlersToString(arr) {
        var s =
            '[' +
            arr
                .map(function map(b) {
                    return b.name || 'function';
                })
                .join(', ') +
            ']';

        return s;
    }

    str += sprintf(LINE_FMT, 'Accepts', this.acceptable.join(', '));
    str += sprintf(LINE_FMT, 'Name', this.name);
    str += sprintf(LINE_FMT, 'Pre', handlersToString(this.before));
    str += sprintf(LINE_FMT, 'Router', this.router.toString());
    str += sprintf(LINE_FMT, 'Routes', '');
    Object.keys(this.routes).forEach(function forEach(k) {
        var handlers = handlersToString(self.routes[k]);
        str += sprintf(SUB_LINE_FMT, k, handlers);
    });
    str += sprintf(LINE_FMT, 'Secure', this.secure);
    str += sprintf(LINE_FMT, 'Url', this.url);
    str += sprintf(
        LINE_FMT,
        'Version',
        Array.isArray(this.versions) ? this.versions.join() : this.versions
    );

    return str;
};

///--- Private methods

// Lifecycle:
//
// 1. _onRequest (new request)
//    2. _setupRequest (decorate req and res objects)
//      3. _afterRoute (runs after route handler finished)
//      4. _finishReqResCycle (on response "finish" and "error" events)
//           5. after hooks
//           6. end

/**
 * Setup request and calls _handle to run middlewares and call router
 *
 * @private
 * @memberof Server
 * @instance
 * @function _onRequest
 * @param    {Object}    req - the request object
 * @param    {Object}    res - the response object
 * @returns  {undefined} no return value
 * @fires Request,Response#request
 */
Server.prototype._onRequest = function _onRequest(req, res) {
    var self = this;

    this.emit('request', req, res);

    // Skip Socket.io endpoints
    if (this.socketio && /^\/socket\.io.*/.test(req.url)) {
        return;
    }

    // Decorate req and res objects
    self._setupRequest(req, res);

    // increment number of requests
    self._inflightRequests++;

    // emit 'pre' event before we run the pre handlers
    self.emit('pre', req, res);

    // Router
    self.router.lookup(req, res);

    // Lifecycle events
    res.once('finish', function onceFinish() {
        self._finishReqResCycle(req, res, res.err);
    });
    res.once('error', function onceError(err) {
        self._finishReqResCycle(req, res, err);
    });
};

/**
 * Set up the request before routing and execution of handler chain functions.
 *
 * @private
 * @memberof Server
 * @instance
 * @function _setupRequest
 * @param    {Object}    req - the request object
 * @param    {Object}    res - the response object
 * @returns  {undefined} no return value
 */
Server.prototype._setupRequest = function _setupRequest(req, res) {
    var self = this;

    // Extend request
    req.log = res.log = self.log;
    req._time = process.hrtime();
    req.serverName = self.name;

    // Extend response
    res.acceptable = self.acceptable;
    res.formatters = self.formatters;
    res.req = req;
    res.serverName = self.name;

    // set header only if name isn't empty string
    if (self.name !== '') {
        res.setHeader('Server', self.name);
    }

    // TODO: revisit, version
    // res.version = self.router.versions[self.router.versions.length - 1];
};

/**
 * After route handlers finished
 *
 * @private
 * @memberof Server
 * @instance
 * @function _afterRoute
 * @param  {Error|undefined} err - router handler error
 * @param  {Request} req - request
 * @param  {Response} res - response
 * @returns {undefined} no return value
 */
Server.prototype._afterRoute = function _afterRoute(err, req, res) {
    var self = this;
    var route = req.route;

    // Preserve handler err for finish event
    res.err = res.err || err;

    // emit 'routed' event after the req has been routed
    self.emit('routed', req, res, route);

    // Error happened in router handlers
    if (err) {
        self._routeErrorResponse(req, res, err);
    }
};

/**
 * Wrapper method for emitting the after event. this is needed in scenarios
 * where the async formatter has failed, and the ot assume that the
 * original res.send() status code is no longer valid (it is now a 500). check
 * if the response is finished, and if not, wait for it before firing the
 * response object.
 *
 * @private
 * @memberof Server
 * @instance
 * @function _finishReqResCycle
 * @param {Object} req - the request object
 * @param {Object} res - the response object
 * @param {Object} [err] - a possible error as a result of failed route matching
 * or failed execution of the handler array.
 * @returns {undefined} no return value
 */
Server.prototype._finishReqResCycle = function _finishReqResCycle(
    req,
    res,
    err
) {
    var self = this;
    var route = req.route; // can be undefined when 404 or error

    // res.finished is set by node core's response object, when
    // res.end() completes. if the request was closed by the client, then emit
    // regardless of res status.

    // after event has signature of function(req, res, route, err) {...}
    if (!res.finished && !_reqClosed(req)) {
        res.once('finish', function resFinished() {
            self.emit('after', req, res, route, err || res.formatterErr);
        });
    } else {
        // if there was an error in the processing of that request, use it.
        // if not, check to see if the request was closed or aborted early and
        // create an error out of that for audit logging.
        var afterErr = err;

        if (!afterErr) {
            if (req._connectionState === 'close') {
                afterErr = new errors.RequestCloseError();
            } else if (req._connectionState === 'aborted') {
                afterErr = new errors.RequestAbortedError();
            }
        }

        self.emit('after', req, res, route, afterErr);
    }

    // decrement number of requests
    self._inflightRequests--;
};

/**
 * Helper function to, when on router error, emit error events and then
 * flush the err.
 *
 * @private
 * @memberof Server
 * @instance
 * @function _routeErrorResponse
 * @param    {Request}     req -    the request object
 * @param    {Response}    res -    the response object
 * @param    {Error}       err -    error
 * @returns  {undefined} no return value
 */
Server.prototype._routeErrorResponse = function _routeErrorResponse(
    req,
    res,
    err
) {
    var self = this;

    // if (self.handleUncaughtExceptions) {
    if (self.listenerCount('uncaughtException') > 1) {
        self.emit('uncaughtException', req, res, req.route, err);
        return;
    }

    self._emitErrorEvents(req, res, null, err, function emitError(emitErr) {
        res.send(emitErr || err);
    });
};

/**
 * Emit error events when errors are encountered either while attempting to
 * route the request (via router) or while executing the handler chain.
 *
 * @private
 * @memberof Server
 * @instance
 * @function _emitErrorEvents
 * @param    {Object} req -    the request object
 * @param    {Object} res -    the response object
 * @param    {Object} route -  the current route, if applicable
 * @param    {Object} err -    an error object
 * @param    {Object} cb -     callback function
 * @returns  {undefined} no return value
 * @fires Error#restifyError
 */
Server.prototype._emitErrorEvents = function _emitErrorEvents(
    req,
    res,
    route,
    err,
    cb
) {
    var self = this;
    var errName = errEvtNameFromError(err);

    req.log.trace(
        {
            err: err,
            errName: errName
        },
        'entering emitErrorEvents',
        err.name
    );

    var errEvtNames = [];

    // if we have listeners for the specific error, fire those first.
    if (self.listeners(errName).length > 0) {
        errEvtNames.push(errName);
    }

    // or if we have a generic error listener. always fire generic error event
    // listener afterwards.
    if (self.listeners('restifyError').length > 0) {
        errEvtNames.push('restifyError');
    }

    // kick off the async listeners
    return vasync.forEachPipeline(
        {
            inputs: errEvtNames,
            func: function emitError(errEvtName, vasyncCb) {
                self.emit(errEvtName, req, res, err, function emitErrDone() {
                    // the error listener may return arbitrary objects, throw
                    // them away and continue on. don't want vasync to take
                    // that error and stop, we want to emit every single event.
                    return vasyncCb();
                });
            }
        },
        // eslint-disable-next-line handle-callback-err
        function onResult(nullErr, results) {
            // vasync will never return error here. callback with the original
            // error to pass it on.
            return cb(err);
        }
    );
};

///--- Helpers

/**
 * Helper function that returns true if the request was closed or aborted.
 *
 * @private
 * @function _reqClosed
 * @param {Object} req - the request object
 * @returns {Boolean} is req closed or aborted
 */
function _reqClosed(req) {
    return (
        req._connectionState === 'close' || req._connectionState === 'aborted'
    );
}

/**
 * Verify and flatten a nested array of request handlers.
 *
 * @private
 * @function argumentsToChain
 * @throws   {TypeError}
 * @param    {Function[]} handlers - pass through of funcs from server.[method]
 * @returns  {Array} request handlers
 */
function argumentsToChain(handlers) {
    assert.array(handlers, 'handlers');

    var chain = [];

    // A recursive function for unwinding a nested array of handlers into a
    // single chain.
    function process(array) {
        for (var i = 0; i < array.length; i++) {
            if (Array.isArray(array[i])) {
                // Recursively call on nested arrays
                process(array[i]);
                continue;
            }
            // If an element of the array isn't an array, ensure it is a
            // handler function and then push it onto the chain of handlers
            assert.func(array[i], 'handler');
            chain.push(array[i]);
        }

        return chain;
    }

    // Return the chain, note that if `handlers` is an empty array, this will
    // return an empty array.
    return process(handlers);
}

/**
 * merge optional formatters with the default formatters to create a single
 * formatters object. the passed in optional formatters object looks like:
 * formatters: {
 *   'application/foo': function formatFoo(req, res, body) {...}
 * }
 * @private
 * @function mergeFormatters
 * @param    {Object} fmt user specified formatters object
 * @returns  {Object}
 */

function mergeFormatters(fmt) {
    var arr = [];
    var obj = {};

    function addFormatter(src, k) {
        assert.func(src[k], 'formatter');

        var q = 1.0; // RFC 2616 sec14 - The default value is q=1
        var t = k;

        if (k.indexOf(';') !== -1) {
            var tmp = k.split(/\s*;\s*/);
            t = tmp[0];

            if (tmp[1].indexOf('q=') !== -1) {
                q = parseFloat(tmp[1].split('=')[1]);
            }
        }

        if (k.indexOf('/') === -1) {
            k = mime.lookup(k);
        }

        obj[t] = src[k];
        arr.push({
            q: q,
            t: t
        });
    }

    Object.keys(formatters).forEach(addFormatter.bind(this, formatters));
    Object.keys(fmt || {}).forEach(addFormatter.bind(this, fmt || {}));

    arr = arr
        .sort(function sort(a, b) {
            return b.q - a.q;
        })
        .map(function map(a) {
            return a.t;
        });

    return {
        formatters: obj,
        acceptable: arr
    };
}

/**
 * Map an Error's .name property into the actual event name that is emitted
 * by the restify server object.
 *
 * @function
 * @private errEvtNameFromError
 * @param {Object} err - an error object
 * @returns {String} an event name to emit
 */
function errEvtNameFromError(err) {
    if (err.name === 'ResourceNotFoundError') {
        // remap the name for router errors
        return 'NotFound';
    } else if (err.name === 'InvalidVersionError') {
        // remap the name for router errors
        return 'VersionNotAllowed';
    } else {
        // TODO: revisit
        return err.name ? err.name.replace(/Error$/, '') : 'Error';
    }
}

/**
 * Mounts a chain on the given path against this HTTP verb
 *
 * @private
 * @function serverMethodFactory
 * @param {String} method - name of the HTTP method
 * @returns {Function} factory
 */
function serverMethodFactory(method) {
    return function serverMethod(opts) {
        if (opts instanceof RegExp || typeof opts === 'string') {
            opts = {
                path: opts
            };
        } else if (typeof opts === 'object') {
            opts = shallowCopy(opts);
        } else {
            throw new TypeError('path (string) required');
        }

        if (arguments.length < 2) {
            throw new TypeError('handler (function) required');
        }

        opts.method = method;
        opts.versions = opts.versions || opts.version || this.versions;
        opts.path = opts.path || opts.url;

        if (!Array.isArray(opts.versions)) {
            opts.versions = [opts.versions];
        }

        // TODO: revisit
        if (!opts.name) {
            opts.name = method + '-' + (opts.path || opts.url);

            if (opts.versions.length > 0) {
                opts.name += '-' + opts.versions.join('--');
            }

            opts.name = opts.name.replace(/\W/g, '').toLowerCase();

            if (this.router.mounts[opts.name]) {
                // GH-401
                opts.name += uuid.v4().substr(0, 7);
            }
        }

        var serverChain = this.chain;
        // We accept both a variable number of handler functions, a
        // variable number of nested arrays of handler functions, or a mix
        // of both
        var handlers = Array.prototype.slice.call(arguments, 1);
        var routeChain = argumentsToChain(handlers);
        var chain = Array.prototype.concat.call(
            this.before,
            serverChain,
            routeChain
        );
        var route = this.router.mount(opts, chain, this._afterRoute.bind(this));

        return route.name;
    };
}
